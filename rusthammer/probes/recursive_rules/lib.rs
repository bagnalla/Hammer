//! Private closed-grammar lowering and left-recursion experiment.
//! This is evidence for a design, not a RustHammer API or verified backend.
#![no_std]

extern crate alloc;
use alloc::vec::Vec;
use core::marker::PhantomData;
pub use rusthammer::BitSpan as Span;
pub use rusthammer::{BitOrder, ByteOrder, Cursor, InputStatus, Order, ParseContext, ParseError};
use rusthammer::{BitSpan, Byte, BytePattern, Epsilon, Literal, ParseOutcome, Parser, WithOrder};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fault {
    InvalidGrammar,
    WorkspaceLimit,
    StepLimit,
    StackLimit,
    InvalidCursor,
    Invariant,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Answer<T> {
    Success(Cursor, T),
    Error(ParseError),
    NeedMore,
    Fatal(Fault),
}

fn primitive<T>(answer: ParseOutcome<T>) -> Answer<T> {
    match answer {
        ParseOutcome::Success(cursor, value) => Answer::Success(cursor, value),
        ParseOutcome::Error(error) => Answer::Error(error),
        ParseOutcome::NeedMore => Answer::NeedMore,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Number,
    Input,
    Pattern,
}

// A finite, schema-specific sum, not Any or a uniform public AST. A production
// lowerer generates its alternatives from the admitted grammar's value types.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Value {
    Number(usize),
    Input(Cursor, Cursor, BitOrder),
    Pattern(usize),
}

type Outcome = Answer<Value>;

// Replay stored values without depending on the mutable workspace's lifetime.
// Borrowed views have checked, source-relative coordinates in this schema.
fn replay(answer: &Outcome) -> Outcome {
    match answer {
        Answer::Success(cursor, value) => {
            let value = match value {
                Value::Number(n) => Value::Number(*n),
                Value::Input(start, end, direction) => Value::Input(*start, *end, *direction),
                Value::Pattern(length) => Value::Pattern(*length),
            };
            Answer::Success(*cursor, value)
        }
        Answer::Error(error) => Answer::Error(*error),
        Answer::NeedMore => Answer::NeedMore,
        Answer::Fatal(fault) => Answer::Fatal(*fault),
    }
}

pub struct Number;
pub struct Input;
pub struct Pattern;

// These tokens never leave the private construction fixtures. Public proposals
// bind exported rule references to a compiled grammar, not raw unbranded indices.
struct Expr<K> {
    id: usize,
    marker: PhantomData<K>,
}
impl<K> Copy for Expr<K> {}
impl<K> Clone for Expr<K> {
    fn clone(&self) -> Self {
        *self
    }
}
struct Rule<K> {
    id: usize,
    marker: PhantomData<K>,
}
impl<K> Copy for Rule<K> {}
impl<K> Clone for Rule<K> {
    fn clone(&self) -> Self {
        *self
    }
}

#[derive(Clone, Copy)]
enum Combine {
    Add,
    Subtract,
    Second,
}

#[derive(Clone, Copy)]
enum Op {
    Empty,
    Digit,
    Literal(u8, u64),
    Pattern(usize),
    Call(usize),
    Seq(usize, usize, Combine),
    Choice(usize, usize),
    Recognize(usize),
    Length(usize),
    Order(usize, Order),
    Erase(usize),
}

#[derive(Clone, Copy)]
struct Node {
    kind: Kind,
    op: Op,
}
struct Definition {
    kind: Kind,
    body: Option<usize>,
}

struct Program {
    nodes: Vec<Node>,
    rules: Vec<Definition>,
}

impl Program {
    fn new() -> Self {
        Self {
            nodes: Vec::new(),
            rules: Vec::new(),
        }
    }
    fn reserve<K>(&mut self, kind: Kind) -> Rule<K> {
        let id = self.rules.len();
        self.rules.push(Definition { kind, body: None });
        Rule {
            id,
            marker: PhantomData,
        }
    }
    fn add<K>(&mut self, kind: Kind, op: Op) -> Expr<K> {
        let id = self.nodes.len();
        self.nodes.push(Node { kind, op });
        Expr {
            id,
            marker: PhantomData,
        }
    }
    fn bind<K>(&mut self, rule: Rule<K>, body: Expr<K>) {
        self.rules[rule.id].body = Some(body.id);
    }
    fn call<K>(&mut self, rule: Rule<K>) -> Expr<K> {
        let kind = self.rules[rule.id].kind;
        self.add(kind, Op::Call(rule.id))
    }
    fn empty(&mut self) -> Expr<Number> {
        self.add(Kind::Number, Op::Empty)
    }
    fn literal(&mut self, width: u8, value: u64) -> Expr<Number> {
        self.add(Kind::Number, Op::Literal(width, value))
    }
    fn seq(&mut self, first: Expr<Number>, second: Expr<Number>) -> Expr<Number> {
        self.add(Kind::Number, Op::Seq(first.id, second.id, Combine::Add))
    }
    fn choice<K>(&mut self, first: Expr<K>, second: Expr<K>) -> Expr<K> {
        let kind = self.nodes[first.id].kind;
        self.add(kind, Op::Choice(first.id, second.id))
    }
    fn recognize<K>(&mut self, child: Expr<K>) -> Expr<Input> {
        self.add(Kind::Input, Op::Recognize(child.id))
    }
    fn length<K>(&mut self, child: Expr<K>) -> Expr<Number> {
        self.add(Kind::Number, Op::Length(child.id))
    }
    fn order<K>(&mut self, child: Expr<K>, order: Order) -> Expr<K> {
        let kind = self.nodes[child.id].kind;
        self.add(kind, Op::Order(child.id, order))
    }
    fn pattern(&mut self, length: usize) -> Expr<Pattern> {
        self.add(Kind::Pattern, Op::Pattern(length))
    }

    // All structural edges point to an earlier instruction. Rule calls are the
    // only cyclic edges and have an output-kind check. Rule identities are slots
    // in this immutable program; equal types/configurations do not merge them.
    fn valid(&self) -> bool {
        let mut i = 0;
        while i < self.nodes.len() {
            let node = self.nodes[i];
            let valid = match node.op {
                Op::Empty | Op::Digit => node.kind == Kind::Number,
                Op::Literal(width, value) => {
                    node.kind == Kind::Number
                        && width <= 64
                        && (width == 64 || value < (1u64 << width))
                }
                Op::Pattern(_) => node.kind == Kind::Pattern,
                Op::Call(rule) => rule < self.rules.len() && self.rules[rule].kind == node.kind,
                Op::Seq(a, b, _) => {
                    a < i
                        && b < i
                        && node.kind == Kind::Number
                        && self.nodes[a].kind == Kind::Number
                        && self.nodes[b].kind == Kind::Number
                }
                Op::Choice(a, b) => {
                    a < i
                        && b < i
                        && self.nodes[a].kind == node.kind
                        && self.nodes[b].kind == node.kind
                }
                Op::Recognize(child) => child < i && node.kind == Kind::Input,
                Op::Erase(child) => child < i && node.kind == Kind::Number,
                Op::Length(child) => {
                    child < i
                        && node.kind == Kind::Number
                        && (self.nodes[child].kind == Kind::Input
                            || self.nodes[child].kind == Kind::Pattern)
                }
                Op::Order(child, _) => child < i && node.kind == self.nodes[child].kind,
            };
            if !valid {
                return false;
            }
            i += 1;
        }
        self.valid_rules()
    }

    // Separate consecutive returning loops for the pinned Aeneas prepass.
    fn valid_rules(&self) -> bool {
        let mut j = 0;
        while j < self.rules.len() {
            match self.rules[j].body {
                Some(body) => {
                    if body >= self.nodes.len() || self.nodes[body].kind != self.rules[j].kind {
                        return false;
                    }
                }
                None => return false,
            }
            j += 1;
        }
        true
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Tag {
    Empty,
    Left,
    Right,
}

struct Entry {
    tag: Tag,
    answer: Outcome,
    head: Option<usize>,
}

#[derive(Clone, Copy)]
enum Frame {
    Idle,
    Eval(usize, Cursor, ParseContext),
    Sequence(usize, ParseContext, Combine),
    Sum(usize, Combine),
    Alternative(usize, Cursor, ParseContext),
    Capture(Cursor, BitOrder),
    Length,
    Erase,
    OrderExit(Order, Order),
    Finish(usize, Cursor, ParseContext),
    Store(usize),
    Grow(usize, Cursor, ParseContext),
}

// The interpreter only indexes pre-sized storage; it never grows a Vec. The
// private allocation helper below is NOT evidence of recoverable allocator
// failure. The proposed production entry accepts caller-provided workspace.
struct Workspace {
    entries: Vec<Entry>,
    best: Vec<Outcome>,
    heads: Vec<Option<usize>>,
    involved: Vec<u64>,
    evaluate: Vec<u64>,
    active: Vec<usize>,
    active_len: usize,
    frames: Vec<Frame>,
    frame_len: usize,
    symbols: usize,
    steps: usize,
    step_limit: usize,
}

fn get_bit(words: &[u64], index: usize) -> bool {
    (words[index / 64] & (1u64 << (index % 64))) != 0
}
fn set_bit(words: &mut [u64], index: usize, value: bool) {
    let mask = 1u64 << (index % 64);
    if value {
        words[index / 64] |= mask;
    } else {
        words[index / 64] &= !mask;
    }
}

fn position(cursor: Cursor, length: usize) -> Option<usize> {
    if cursor.bit >= 8 || cursor.byte > length || (cursor.byte == length && cursor.bit != 0) {
        return None;
    }
    // Checked workspace indexing, never an unchecked absolute bit-position used
    // to establish parsing progress. Progress compares the cursor pair directly.
    match cursor.byte.checked_mul(8) {
        Some(base) => base.checked_add(usize::from(cursor.bit)),
        None => None,
    }
}
fn context_id(context: ParseContext) -> usize {
    let bit = match context.order.bit {
        BitOrder::HighFirst => 0,
        BitOrder::LowFirst => 1,
    };
    let byte = match context.order.byte {
        ByteOrder::Big => 0,
        ByteOrder::Little => 2,
    };
    let status = match context.status {
        InputStatus::Final => 0,
        InputStatus::Partial => 4,
    };
    bit + byte + status
}

struct Layout {
    positions: usize,
    symbols: usize,
    entries: usize,
    set_bits: usize,
    set_words: usize,
}
fn layout(length: usize, rules: usize) -> Result<Layout, Fault> {
    let bytes = length.checked_add(1).ok_or(Fault::WorkspaceLimit)?;
    let positions = bytes.checked_mul(8).ok_or(Fault::WorkspaceLimit)?;
    let symbols = rules.checked_mul(8).ok_or(Fault::WorkspaceLimit)?;
    let entries = positions
        .checked_mul(symbols)
        .ok_or(Fault::WorkspaceLimit)?;
    let set_bits = entries.checked_mul(symbols).ok_or(Fault::WorkspaceLimit)?;
    let set_words = set_bits.checked_add(63).ok_or(Fault::WorkspaceLimit)? / 64;
    Ok(Layout {
        positions,
        symbols,
        entries,
        set_bits,
        set_words,
    })
}

impl Workspace {
    fn allocate(
        length: usize,
        rules: usize,
        cells: usize,
        frames: usize,
        steps: usize,
    ) -> Result<Self, Fault> {
        let layout = layout(length, rules)?;
        let positions = layout.positions;
        let symbols = layout.symbols;
        let entries = layout.entries;
        let set_words = layout.set_words;
        if entries > cells || layout.set_bits > cells || positions > cells || frames > cells {
            return Err(Fault::WorkspaceLimit);
        }
        let mut state = Self {
            entries: Vec::new(),
            best: Vec::new(),
            heads: Vec::new(),
            involved: Vec::new(),
            evaluate: Vec::new(),
            active: Vec::new(),
            active_len: 0,
            frames: Vec::new(),
            frame_len: 0,
            symbols,
            steps,
            step_limit: steps,
        };
        let mut i = 0;
        while i < entries {
            state.entries.push(Entry {
                tag: Tag::Empty,
                answer: Answer::Error(ParseError::Mismatch),
                head: None,
            });
            state.best.push(Answer::Error(ParseError::Mismatch));
            i += 1;
        }
        let mut i = 0;
        while i < positions {
            state.heads.push(None);
            i += 1;
        }
        let mut i = 0;
        while i < set_words {
            state.involved.push(0);
            state.evaluate.push(0);
            i += 1;
        }
        let mut i = 0;
        while i < frames {
            state.frames.push(Frame::Idle);
            state.active.push(0);
            i += 1;
        }
        Ok(state)
    }
    fn prepare(&mut self, length: usize, rules: usize) -> Result<(), Fault> {
        let needed = layout(length, rules)?;
        if self.entries.len() < needed.entries
            || self.best.len() < needed.entries
            || self.heads.len() < needed.positions
            || self.involved.len() < needed.set_words
            || self.evaluate.len() < needed.set_words
        {
            return Err(Fault::WorkspaceLimit);
        }
        self.symbols = needed.symbols;
        self.steps = self.step_limit;
        self.frame_len = 0;
        self.active_len = 0;
        let mut index = 0;
        while index < self.entries.len() {
            self.entries[index].tag = Tag::Empty;
            self.entries[index].head = None;
            self.entries[index].answer = Answer::Error(ParseError::Mismatch);
            self.best[index] = Answer::Error(ParseError::Mismatch);
            index += 1;
        }
        let mut index = 0;
        while index < self.heads.len() {
            self.heads[index] = None;
            index += 1;
        }
        let mut index = 0;
        while index < self.involved.len() {
            self.involved[index] = 0;
            index += 1;
        }
        let mut index = 0;
        while index < self.evaluate.len() {
            self.evaluate[index] = 0;
            index += 1;
        }
        Ok(())
    }
    fn push(&mut self, frame: Frame) -> Result<(), Fault> {
        if self.frame_len == self.frames.len() {
            return Err(Fault::StackLimit);
        }
        self.frames[self.frame_len] = frame;
        self.frame_len += 1;
        Ok(())
    }
    fn pop(&mut self) -> Frame {
        self.frame_len -= 1;
        let frame = self.frames[self.frame_len];
        self.frames[self.frame_len] = Frame::Idle;
        frame
    }
    fn setup(&mut self, slot: usize) {
        let head = match self.entries[slot].head {
            Some(head) => head,
            None => {
                self.entries[slot].head = Some(slot);
                slot
            }
        };
        let mut i = self.active_len;
        while i > 0 {
            i -= 1;
            let involved = self.active[i];
            if involved == slot {
                break;
            }
            self.entries[involved].head = Some(head);
            set_bit(
                &mut self.involved,
                head * self.symbols + involved % self.symbols,
                true,
            );
        }
    }
    fn grow(
        &mut self,
        slot: usize,
        cursor: Cursor,
        context: ParseContext,
        body: usize,
    ) -> Result<(), Fault> {
        let pos = slot / self.symbols;
        self.heads[pos] = Some(slot);
        let mut symbol = 0;
        while symbol < self.symbols {
            let index = slot * self.symbols + symbol;
            let enabled = get_bit(&self.involved, index);
            set_bit(&mut self.evaluate, index, enabled);
            symbol += 1;
        }
        self.best[slot] = replay(&self.entries[slot].answer);
        self.push(Frame::Grow(slot, cursor, context))?;
        self.push(Frame::Eval(body, cursor, context))
    }
}

fn further(first: Cursor, second: Cursor) -> bool {
    first.byte > second.byte || (first.byte == second.byte && first.bit > second.bit)
}

fn root_instruction(program: &Program, root: usize) -> Option<usize> {
    let mut n = 0;
    while n < program.nodes.len() {
        if let Op::Call(rule) = program.nodes[n].op {
            if rule == root {
                return Some(n);
            }
        }
        n += 1;
    }
    None
}

fn run<'i, 'p>(
    program: &Program,
    state: &mut Workspace,
    input: &'i [u8],
    pattern: &'p [u8],
    root: usize,
    start: Cursor,
    context: ParseContext,
) -> Outcome {
    if !program.valid() || root >= program.rules.len() {
        return Answer::Fatal(Fault::InvalidGrammar);
    }
    if position(start, input.len()).is_none() {
        return Answer::Fatal(Fault::InvalidCursor);
    }
    if let Err(fault) = state.prepare(input.len(), program.rules.len()) {
        return Answer::Fatal(fault);
    }
    // Enter through the same rule-call instruction as all recursive invocations.
    let root_node = match root_instruction(program, root) {
        Some(node) => node,
        None => return Answer::Fatal(Fault::InvalidGrammar),
    };
    if let Err(fault) = state.push(Frame::Eval(root_node, start, context)) {
        return Answer::Fatal(fault);
    }
    let mut answer = Answer::Error(ParseError::Mismatch);
    // Keep the termination check inside the loop: the pinned Aeneas prepass
    // rejects the equivalent while-loop with these returning branches.
    loop {
        if state.frame_len == 0 {
            return answer;
        }
        match &answer {
            Answer::Fatal(_) | Answer::NeedMore => return answer,
            Answer::Error(error) if !error.is_recoverable() => return answer,
            _ => {}
        }
        if state.steps == 0 {
            return Answer::Fatal(Fault::StepLimit);
        }
        state.steps -= 1;
        answer = match step(program, state, input, pattern, answer) {
            Ok(next) => next,
            Err(fault) => return Answer::Fatal(fault),
        };
    }
}

fn step<'i, 'p>(
    program: &Program,
    state: &mut Workspace,
    input: &'i [u8],
    pattern: &'p [u8],
    mut answer: Outcome,
) -> Result<Outcome, Fault> {
    match state.pop() {
        Frame::Idle => return Err(Fault::Invariant),
        Frame::Eval(node, cursor, context) => match program.nodes[node].op {
            Op::Empty => answer = Answer::Success(cursor, Value::Number(0)),
            Op::Digit => {
                answer = match Byte.parse_with(input, cursor, context) {
                    ParseOutcome::Success(next, byte) => {
                        if byte >= b'0' && byte <= b'9' {
                            Answer::Success(next, Value::Number(usize::from(byte - b'0')))
                        } else {
                            Answer::Error(ParseError::Mismatch)
                        }
                    }
                    ParseOutcome::Error(error) => Answer::Error(error),
                    ParseOutcome::NeedMore => Answer::NeedMore,
                };
            }
            Op::Literal(width, value) => {
                let literal = Literal::new(width, value).map_err(|_| Fault::InvalidGrammar)?;
                answer = match primitive(literal.parse_with(input, cursor, context)) {
                    Answer::Success(next, _) => Answer::Success(next, Value::Number(1)),
                    Answer::Error(error) => Answer::Error(error),
                    Answer::NeedMore => Answer::NeedMore,
                    Answer::Fatal(fault) => Answer::Fatal(fault),
                };
            }
            Op::Pattern(length) => {
                if length > pattern.len() {
                    return Err(Fault::InvalidGrammar);
                }
                let pattern = &pattern[..length];
                answer =
                    match primitive(BytePattern::new(pattern).parse_with(input, cursor, context)) {
                        Answer::Success(next, _) => Answer::Success(next, Value::Pattern(length)),
                        Answer::Error(error) => Answer::Error(error),
                        Answer::NeedMore => Answer::NeedMore,
                        Answer::Fatal(fault) => Answer::Fatal(fault),
                    };
            }
            Op::Seq(first, second, combine) => {
                state.push(Frame::Sequence(second, context, combine))?;
                state.push(Frame::Eval(first, cursor, context))?;
            }
            Op::Choice(first, second) => {
                state.push(Frame::Alternative(second, cursor, context))?;
                state.push(Frame::Eval(first, cursor, context))?;
            }
            Op::Erase(child) => {
                state.push(Frame::Erase)?;
                state.push(Frame::Eval(child, cursor, context))?;
            }
            Op::Recognize(child) => {
                state.push(Frame::Capture(cursor, context.order.bit))?;
                state.push(Frame::Eval(child, cursor, context))?;
            }
            Op::Length(child) => {
                state.push(Frame::Length)?;
                state.push(Frame::Eval(child, cursor, context))?;
            }
            Op::Order(child, order) => {
                let guard = WithOrder {
                    parser: Epsilon,
                    order,
                };
                match guard.parse_with(input, cursor, context) {
                    ParseOutcome::Success(_, _) => {
                        state.push(Frame::OrderExit(context.order, order))?;
                        state.push(Frame::Eval(
                            child,
                            cursor,
                            ParseContext {
                                order,
                                status: context.status,
                            },
                        ))?;
                    }
                    ParseOutcome::Error(error) => answer = Answer::Error(error),
                    ParseOutcome::NeedMore => answer = Answer::NeedMore,
                }
            }
            Op::Call(rule) => {
                let pos = position(cursor, input.len()).ok_or(Fault::InvalidCursor)?;
                let symbol = rule * 8 + context_id(context);
                let slot = pos * state.symbols + symbol;
                let body = program.rules[rule].body.ok_or(Fault::InvalidGrammar)?;
                if let Some(head) = state.heads[pos] {
                    let set = head * state.symbols + symbol;
                    if state.entries[slot].tag == Tag::Empty
                        && slot != head
                        && !get_bit(&state.involved, set)
                    {
                        answer = Answer::Error(ParseError::Mismatch);
                        return Ok(answer);
                    }
                    if get_bit(&state.evaluate, set) {
                        set_bit(&mut state.evaluate, set, false);
                        state.push(Frame::Store(slot))?;
                        state.push(Frame::Eval(body, cursor, context))?;
                        return Ok(answer);
                    }
                }
                match state.entries[slot].tag {
                    Tag::Empty => {
                        state.entries[slot].tag = Tag::Left;
                        state.entries[slot].head = None;
                        state.entries[slot].answer = Answer::Error(ParseError::Mismatch);
                        if state.active_len == state.active.len() {
                            return Err(Fault::StackLimit);
                        }
                        state.active[state.active_len] = slot;
                        state.active_len += 1;
                        state.push(Frame::Finish(slot, cursor, context))?;
                        state.push(Frame::Eval(body, cursor, context))?;
                    }
                    Tag::Left => {
                        state.setup(slot);
                        answer = replay(&state.entries[slot].answer);
                    }
                    Tag::Right => answer = replay(&state.entries[slot].answer),
                }
            }
        },
        Frame::Sequence(second, context, combine) => {
            if let Answer::Success(cursor, value) = &mut answer {
                let count = match value {
                    Value::Number(count) => *count,
                    _ => return Err(Fault::Invariant),
                };
                let next = *cursor;
                state.push(Frame::Sum(count, combine))?;
                state.push(Frame::Eval(second, next, context))?;
            }
        }
        Frame::Sum(first, combine) => {
            if let Answer::Success(_, value) = &mut answer {
                match value {
                    Value::Number(second) => match match combine {
                        Combine::Add => first.checked_add(*second),
                        Combine::Subtract => first.checked_sub(*second),
                        Combine::Second => Some(*second),
                    } {
                        Some(sum) => *second = sum,
                        None => {
                            answer = Answer::Error(match combine {
                                Combine::Subtract => ParseError::Mismatch,
                                _ => ParseError::CountOverflow,
                            })
                        }
                    },
                    _ => return Err(Fault::Invariant),
                }
            }
        }
        Frame::Alternative(second, cursor, context) => {
            if let Answer::Error(error) = &mut answer {
                if error.is_recoverable() {
                    state.push(Frame::Eval(second, cursor, context))?;
                }
            }
        }
        Frame::Capture(start, direction) => {
            if let Answer::Success(end, _) = answer {
                answer = match BitSpan::new(input, start, end, direction) {
                    Ok(_) => Answer::Success(end, Value::Input(start, end, direction)),
                    Err(error) => Answer::Error(error),
                };
            }
        }
        Frame::Length => {
            if let Answer::Success(_, value) = &mut answer {
                let count = match value {
                    Value::Input(start, end, _) => {
                        if start.bit != 0 || end.bit != 0 {
                            return Ok(Answer::Error(ParseError::Unaligned));
                        }
                        end.byte - start.byte
                    }
                    Value::Pattern(length) => *length,
                    _ => return Err(Fault::Invariant),
                };
                *value = Value::Number(count);
            }
        }
        Frame::Erase => {
            if let Answer::Success(cursor, _) = answer {
                answer = Answer::Success(cursor, Value::Number(0));
            }
        }
        Frame::OrderExit(outer, inner) => {
            if let Answer::Success(cursor, _) = &mut answer {
                if outer.bit != inner.bit && cursor.bit != 0 {
                    answer = Answer::Error(ParseError::Unaligned);
                }
            }
        }
        Frame::Store(slot) => {
            state.entries[slot].tag = Tag::Right;
            state.entries[slot].answer = replay(&answer);
        }
        Frame::Finish(slot, cursor, context) => {
            if state.active_len == 0 || state.active[state.active_len - 1] != slot {
                return Err(Fault::Invariant);
            }
            state.active_len -= 1;
            state.entries[slot].answer = replay(&answer);
            match state.entries[slot].head {
                None => state.entries[slot].tag = Tag::Right,
                Some(head) => {
                    if head == slot {
                        state.entries[slot].tag = Tag::Right;
                        if let Answer::Success(_, _) = &mut answer {
                            let body = program.rules[(slot % state.symbols) / 8]
                                .body
                                .ok_or(Fault::InvalidGrammar)?;
                            state.grow(slot, cursor, context, body)?;
                        }
                    }
                }
            }
        }
        Frame::Grow(slot, cursor, context) => {
            let best = replay(&state.best[slot]);
            let advance = match (&answer, &best) {
                (Answer::Success(next, _), Answer::Success(old, _)) => further(*next, *old),
                _ => false,
            };
            if advance {
                state.entries[slot].answer = replay(&answer);
                let body = program.rules[(slot % state.symbols) / 8]
                    .body
                    .ok_or(Fault::InvalidGrammar)?;
                state.grow(slot, cursor, context, body)?;
            } else {
                state.heads[slot / state.symbols] = None;
                state.entries[slot].answer = replay(&best);
                answer = best;
            }
        }
    }
    Ok(answer)
}

fn number(answer: Outcome) -> Answer<usize> {
    match answer {
        Answer::Success(cursor, value) => match value {
            Value::Number(n) => Answer::Success(cursor, n),
            _ => Answer::Fatal(Fault::Invariant),
        },
        Answer::Error(error) => Answer::Error(error),
        Answer::NeedMore => Answer::NeedMore,
        Answer::Fatal(fault) => Answer::Fatal(fault),
    }
}
fn span_value(input: &[u8], answer: Outcome) -> Answer<BitSpan<'_>> {
    match answer {
        Answer::Success(cursor, value) => match value {
            Value::Input(start, end, direction) => match BitSpan::new(input, start, end, direction)
            {
                Ok(span) => Answer::Success(cursor, span),
                Err(error) => Answer::Error(error),
            },
            _ => Answer::Fatal(Fault::Invariant),
        },
        Answer::Error(error) => Answer::Error(error),
        Answer::NeedMore => Answer::NeedMore,
        Answer::Fatal(fault) => Answer::Fatal(fault),
    }
}
fn input_value(input: &[u8], answer: Outcome) -> Answer<&[u8]> {
    match span_value(input, answer) {
        Answer::Success(cursor, span) => match span.as_bytes() {
            Some(bytes) => Answer::Success(cursor, bytes),
            None => Answer::Error(ParseError::Unaligned),
        },
        Answer::Error(error) => Answer::Error(error),
        Answer::NeedMore => Answer::NeedMore,
        Answer::Fatal(fault) => Answer::Fatal(fault),
    }
}

// A finite fixture selector, not the proposed user-facing grammar API.
// 0: A <- A 'a' / 'a'
// 1: A <- B 'a' / 'a'; B <- A
// 2: A <- 'a' A / epsilon
// 3: A <- A 'a' / epsilon
// 4: A <- A (no seed)
// 5: A <- A / epsilon (equal-length result)
// 6: A <- B 'a' / 'a'; B <- recognize(A), with B -> length at use
// 8: A <- '(' A ')' A / epsilon
// 9: E <- E '-' digit / digit, computing checked subtraction
// 7: A(big) <- B(little) 'a' / 'a'; B <- A(big)
fn grammar(mode: u8) -> (Program, Rule<Number>) {
    let mut p = Program::new();
    let a = p.reserve(Kind::Number);
    let call_a = p.call(a);
    let token = if mode == 10 {
        p.literal(1, 1)
    } else {
        p.literal(8, u64::from(b'a'))
    };
    let empty = p.empty();
    let recursive = if mode == 1 || mode == 7 {
        let b: Rule<Number> = p.reserve(Kind::Number);
        let body = if mode == 7 {
            p.order(call_a, Order::DEFAULT)
        } else {
            call_a
        };
        p.bind(b, body);
        let call_b = p.call(b);
        if mode == 7 {
            p.order(
                call_b,
                Order {
                    bit: BitOrder::HighFirst,
                    byte: ByteOrder::Little,
                },
            )
        } else {
            call_b
        }
    } else if mode == 6 {
        let b: Rule<Input> = p.reserve(Kind::Input);
        let body = p.recognize(call_a);
        p.bind(b, body);
        let call_b = p.call(b);
        p.length(call_b)
    } else {
        call_a
    };
    let body = if mode == 8 {
        let open = p.literal(8, u64::from(b'('));
        let close = p.literal(8, u64::from(b')'));
        let nested = p.seq(open, call_a);
        let closed = p.seq(nested, close);
        let followed = p.seq(closed, call_a);
        p.choice(followed, empty)
    } else if mode == 9 {
        let minus = p.literal(8, u64::from(b'-'));
        let digit: Expr<Number> = p.add(Kind::Number, Op::Digit);
        let right: Expr<Number> = p.add(Kind::Number, Op::Seq(minus.id, digit.id, Combine::Second));
        let difference: Expr<Number> = p.add(
            Kind::Number,
            Op::Seq(call_a.id, right.id, Combine::Subtract),
        );
        p.choice(difference, digit)
    } else if mode == 2 {
        let seq = p.seq(token, call_a);
        p.choice(seq, empty)
    } else if mode == 4 {
        call_a
    } else if mode == 5 {
        p.choice(call_a, empty)
    } else {
        let seq = p.seq(recursive, token);
        let base = if mode == 3 { empty } else { token };
        p.choice(seq, base)
    };
    p.bind(a, body);
    (p, a)
}

pub fn parse(
    mode: u8,
    input: &[u8],
    context: ParseContext,
    frame_limit: usize,
    step_limit: usize,
) -> Answer<usize> {
    let (program, root) = grammar(mode);
    let mut state = match Workspace::allocate(
        input.len(),
        program.rules.len(),
        4_000_000,
        frame_limit,
        step_limit,
    ) {
        Ok(state) => state,
        Err(fault) => return Answer::Fatal(fault),
    };
    number(run(
        &program,
        &mut state,
        input,
        &[],
        root.id,
        Cursor { byte: 0, bit: 0 },
        context,
    ))
}

pub fn borrowed(input: &[u8], context: ParseContext) -> Answer<&[u8]> {
    let (mut program, root) = grammar(1);
    let call = program.call(root);
    let capture = program.recognize(call);
    let bytes: Rule<Input> = program.reserve(Kind::Input);
    program.bind(bytes, capture);
    let _ = program.call(bytes);
    let mut state =
        match Workspace::allocate(input.len(), program.rules.len(), 4_000_000, 256, 100_000) {
            Ok(state) => state,
            Err(fault) => return Answer::Fatal(fault),
        };
    input_value(
        input,
        run(
            &program,
            &mut state,
            input,
            &[],
            bytes.id,
            Cursor { byte: 0, bit: 0 },
            context,
        ),
    )
}

pub fn bit_span(input: &[u8], context: ParseContext) -> Answer<BitSpan<'_>> {
    let (mut program, root) = grammar(10);
    let call = program.call(root);
    let capture = program.recognize(call);
    let span: Rule<Input> = program.reserve(Kind::Input);
    program.bind(span, capture);
    let _ = program.call(span);
    let mut work =
        match Workspace::allocate(input.len(), program.rules.len(), 4_000_000, 256, 100_000) {
            Ok(work) => work,
            Err(fault) => return Answer::Fatal(fault),
        };
    span_value(
        input,
        run(
            &program,
            &mut work,
            input,
            &[],
            span.id,
            Cursor { byte: 0, bit: 0 },
            context,
        ),
    )
}

pub fn pattern<'p>(pattern: &'p [u8], input: &[u8], context: ParseContext) -> Answer<&'p [u8]> {
    let mut program = Program::new();
    let root: Rule<Pattern> = program.reserve(Kind::Pattern);
    let body = program.pattern(pattern.len());
    program.bind(root, body);
    let _ = program.call(root);
    let mut state =
        match Workspace::allocate(input.len(), program.rules.len(), 4_000_000, 64, 10_000) {
            Ok(state) => state,
            Err(fault) => return Answer::Fatal(fault),
        };
    match run(
        &program,
        &mut state,
        input,
        pattern,
        root.id,
        Cursor { byte: 0, bit: 0 },
        context,
    ) {
        Answer::Success(cursor, value) => match value {
            Value::Pattern(length) => {
                if length > pattern.len() {
                    Answer::Fatal(Fault::Invariant)
                } else {
                    Answer::Success(cursor, &pattern[..length])
                }
            }
            _ => Answer::Fatal(Fault::Invariant),
        },
        Answer::Error(error) => Answer::Error(error),
        Answer::NeedMore => Answer::NeedMore,
        Answer::Fatal(fault) => Answer::Fatal(fault),
    }
}

// No Clone or Copy requirement on construction outside memoized rule boundaries.
#[derive(Debug, PartialEq, Eq)]
pub struct Owned {
    pub count: usize,
}
pub fn owned(input: &[u8]) -> Answer<Owned> {
    match parse(1, input, ParseContext::FINAL, 256, 100_000) {
        Answer::Success(cursor, count) => Answer::Success(cursor, Owned { count }),
        Answer::Error(error) => Answer::Error(error),
        Answer::NeedMore => Answer::NeedMore,
        Answer::Fatal(fault) => Answer::Fatal(fault),
    }
}

// This lowerer admits a concrete, permanent source capability: recognition of
// the pure structural subset below. It has no Map/Verify/TryMap/Bind blanket
// implementation, so it cannot accidentally erase an acceptance-affecting action.
// Unit results use Number(0) as their private encoded representation.
struct UnitRef {
    id: usize,
}
impl<'input> rusthammer::Grammar<'input> for UnitRef {
    type Output = ();
}
trait LowerRecognition {
    fn lower(&self, program: &mut Program) -> Expr<Number>;
}
impl LowerRecognition for UnitRef {
    fn lower(&self, program: &mut Program) -> Expr<Number> {
        program.add(Kind::Number, Op::Call(self.id))
    }
}
impl LowerRecognition for Literal {
    fn lower(&self, program: &mut Program) -> Expr<Number> {
        program.literal(self.width(), self.value())
    }
}
impl LowerRecognition for Epsilon {
    fn lower(&self, program: &mut Program) -> Expr<Number> {
        program.empty()
    }
}
impl<P: LowerRecognition> LowerRecognition for rusthammer::Ignore<P> {
    fn lower(&self, program: &mut Program) -> Expr<Number> {
        let child = self.parser.lower(program);
        program.add(Kind::Number, Op::Erase(child.id))
    }
}
impl<P: LowerRecognition, Q: LowerRecognition> LowerRecognition for rusthammer::Seq<P, Q> {
    fn lower(&self, program: &mut Program) -> Expr<Number> {
        let first = self.first.lower(program);
        let second = self.second.lower(program);
        // Only recognition is requested, so intermediate decoded values are
        // discarded. Neither callbacks nor predicates are admitted by this trait.
        program.add(Kind::Number, Op::Seq(first.id, second.id, Combine::Second))
    }
}
impl<P: LowerRecognition, Q: LowerRecognition> LowerRecognition for rusthammer::Choice<P, Q> {
    fn lower(&self, program: &mut Program) -> Expr<Number> {
        let first = self.first.lower(program);
        let second = self.second.lower(program);
        program.choice(first, second)
    }
}
impl<P: LowerRecognition> LowerRecognition for WithOrder<P> {
    fn lower(&self, program: &mut Program) -> Expr<Number> {
        let child = self.parser.lower(program);
        program.order(child, self.order)
    }
}
fn define_unit<'input, P>(program: &mut Program, rule: Rule<Number>, body: &P)
where
    P: rusthammer::Grammar<'input, Output = ()> + LowerRecognition,
{
    let expression = body.lower(program);
    program.bind(rule, expression);
}

/// Construct a recursive body with actual library constructors, lower it once,
/// then execute the closed program. There is no recursive Eval dictionary.
pub fn lowered(input: &[u8], context: ParseContext) -> Answer<&[u8]> {
    let mut program = Program::new();
    let root: Rule<Number> = program.reserve(Kind::Number);
    let token = rusthammer::Ignore {
        parser: Literal::new(8, u64::from(b'a')).unwrap(),
    };
    let recur = rusthammer::Ignore {
        parser: rusthammer::seq(UnitRef { id: root.id }, token),
    };
    let body = rusthammer::choice(recur, token);
    define_unit(&mut program, root, &body);
    let source = rusthammer::Recognize {
        parser: UnitRef { id: root.id },
    };
    let child = source.parser.lower(&mut program);
    let capture = program.recognize(child);
    let output: Rule<Input> = program.reserve(Kind::Input);
    program.bind(output, capture);
    let _ = program.call(output);
    let mut work =
        match Workspace::allocate(input.len(), program.rules.len(), 4_000_000, 256, 100_000) {
            Ok(work) => work,
            Err(fault) => return Answer::Fatal(fault),
        };
    input_value(
        input,
        run(
            &program,
            &mut work,
            input,
            &[],
            output.id,
            Cursor { byte: 0, bit: 0 },
            context,
        ),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(mode: u8, input: &[u8], count: usize) {
        assert_eq!(
            parse(mode, input, ParseContext::FINAL, 512, 100_000),
            Answer::Success(
                Cursor {
                    byte: count,
                    bit: 0
                },
                count
            )
        );
    }
    #[test]
    fn direct_indirect_mutual_and_heterogeneous_recursion() {
        for mode in [0, 1, 2, 3, 6, 7] {
            for count in 1..12 {
                let input = alloc::vec![b'a'; count];
                check(mode, &input, count);
                let mut with_suffix = input.clone();
                with_suffix.push(b'x');
                check(mode, &with_suffix, count);
            }
        }
    }
    #[test]
    fn partial_growth_must_not_return_a_shorter_seed() {
        for mode in [0, 1, 2, 3, 6, 7] {
            assert_eq!(
                parse(mode, b"aaa", ParseContext::PARTIAL, 512, 100_000),
                Answer::NeedMore
            );
            assert_eq!(
                parse(mode, b"aaax", ParseContext::PARTIAL, 512, 100_000),
                Answer::Success(Cursor { byte: 3, bit: 0 }, 3)
            );
            check(mode, b"aaaa", 4);
        }
    }
    #[test]
    fn empty_nullable_equal_length_and_seedless_cycles() {
        check(2, b"", 0);
        check(3, b"", 0);
        check(5, b"aaa", 0);
        assert_eq!(
            parse(4, b"aaa", ParseContext::FINAL, 32, 1000),
            Answer::Error(ParseError::Mismatch)
        );
        assert_eq!(
            parse(0, b"x", ParseContext::FINAL, 32, 1000),
            Answer::Error(ParseError::Mismatch)
        );
    }
    #[test]
    fn nested_structure_and_left_associative_values() {
        check(8, b"(()())()x", 8);
        assert_eq!(
            parse(8, b"(()())", ParseContext::PARTIAL, 256, 100_000),
            Answer::NeedMore
        );
        assert_eq!(
            parse(9, b"9-3-2", ParseContext::FINAL, 256, 100_000),
            Answer::Success(Cursor { byte: 5, bit: 0 }, 4)
        );
        assert_eq!(
            parse(9, b"9-3-", ParseContext::PARTIAL, 256, 100_000),
            Answer::NeedMore
        );
        assert_eq!(
            parse(9, b"9-3-x", ParseContext::FINAL, 256, 100_000),
            Answer::Success(Cursor { byte: 3, bit: 0 }, 6)
        );
    }
    #[test]
    fn resource_failure_is_fatal() {
        assert_eq!(
            parse(0, b"aaa", ParseContext::FINAL, 0, 1000),
            Answer::Fatal(Fault::StackLimit)
        );
        assert_eq!(
            parse(0, b"aaa", ParseContext::FINAL, 256, 0),
            Answer::Fatal(Fault::StepLimit)
        );
        assert!(matches!(
            Workspace::allocate(usize::MAX, 1, 64, 8, 100),
            Err(Fault::WorkspaceLimit)
        ));
        assert!(matches!(
            Workspace::allocate(100, 1, 64, 8, 100),
            Err(Fault::WorkspaceLimit)
        ));
    }
    #[test]
    fn independent_borrows_escape_workspace() {
        let input = *b"aaax";
        let result = borrowed(&input, ParseContext::FINAL);
        match result {
            Answer::Success(cursor, bytes) => {
                assert_eq!(cursor.byte, 3);
                assert_eq!(bytes, b"aaa");
                assert_eq!(bytes.as_ptr(), input.as_ptr());
            }
            _ => panic!("expected borrowed input"),
        }
        let configured = *b"ab";
        let parsed = {
            let short_lived_input = *b"ab!";
            pattern(&configured, &short_lived_input, ParseContext::FINAL)
        };
        match parsed {
            Answer::Success(_, bytes) => assert_eq!(bytes.as_ptr(), configured.as_ptr()),
            _ => panic!("expected configured-pattern borrow"),
        }
        assert_eq!(
            owned(b"aaa"),
            Answer::Success(Cursor { byte: 3, bit: 0 }, Owned { count: 3 })
        );
    }
    #[test]
    fn same_type_different_configuration_and_shared_rule_handles() {
        let mut p = Program::new();
        let root: Rule<Number> = p.reserve(Kind::Number);
        let a: Rule<Number> = p.reserve(Kind::Number);
        let b: Rule<Number> = p.reserve(Kind::Number);
        let a_body = p.literal(8, u64::from(b'a'));
        let b_body = p.literal(8, u64::from(b'b'));
        p.bind(a, a_body);
        p.bind(b, b_body);
        let ca = p.call(a);
        let cb = p.call(b);
        let alternate = p.choice(ca, cb);
        let same_handle = p.call(b);
        let sequence = p.seq(alternate, same_handle);
        p.bind(root, sequence);
        let _ = p.call(root);
        let mut work = Workspace::allocate(2, p.rules.len(), 4_000_000, 64, 1000).unwrap();
        assert_eq!(
            number(run(
                &p,
                &mut work,
                b"bb",
                &[],
                root.id,
                Cursor { byte: 0, bit: 0 },
                ParseContext::FINAL
            )),
            Answer::Success(Cursor { byte: 2, bit: 0 }, 2)
        );
    }
    #[test]
    fn escaping_partial_bit_span() {
        let bytes = [0b1110_0000];
        match bit_span(&bytes, ParseContext::FINAL) {
            Answer::Success(cursor, span) => {
                assert_eq!(cursor, Cursor { byte: 0, bit: 3 });
                assert_eq!(span.input().as_ptr(), bytes.as_ptr());
                assert_eq!(span.start(), Cursor { byte: 0, bit: 0 });
                assert_eq!(span.end(), cursor);
                assert_eq!(span.as_bytes(), None);
            }
            _ => panic!("expected span"),
        }
    }
    #[test]
    fn lowers_actual_structured_combinators() {
        assert_eq!(
            lowered(b"aaax", ParseContext::FINAL),
            Answer::Success(Cursor { byte: 3, bit: 0 }, &b"aaa"[..])
        );
        assert_eq!(lowered(b"aaa", ParseContext::PARTIAL), Answer::NeedMore);
    }
    #[test]
    fn workspace_reuse_starts_a_fresh_session_and_checks_layout() {
        let (program, root) = grammar(1);
        let mut work = Workspace::allocate(2, program.rules.len(), 100_000, 128, 10_000).unwrap();
        let start = Cursor { byte: 0, bit: 0 };
        assert_eq!(
            number(run(
                &program,
                &mut work,
                b"aa",
                &[],
                root.id,
                start,
                ParseContext::PARTIAL
            )),
            Answer::NeedMore
        );
        assert_eq!(
            number(run(
                &program,
                &mut work,
                b"aa",
                &[],
                root.id,
                start,
                ParseContext::FINAL
            )),
            Answer::Success(Cursor { byte: 2, bit: 0 }, 2)
        );
        assert_eq!(
            number(run(
                &program,
                &mut work,
                b"xx",
                &[],
                root.id,
                start,
                ParseContext::FINAL
            )),
            Answer::Error(ParseError::Mismatch)
        );
        assert_eq!(
            number(run(
                &program,
                &mut work,
                b"aaa",
                &[],
                root.id,
                start,
                ParseContext::FINAL
            )),
            Answer::Fatal(Fault::WorkspaceLimit)
        );
    }
    #[test]
    fn malformed_program_is_rejected_before_execution() {
        let mut p = Program::new();
        let unbound: Rule<Number> = p.reserve(Kind::Number);
        let _ = p.call(unbound);
        assert!(!p.valid());
        let wrong = p.pattern(1);
        p.rules[unbound.id].body = Some(wrong.id);
        assert!(!p.valid());
    }
    #[test]
    fn bit_cursor_and_all_contexts() {
        for bit in [BitOrder::HighFirst, BitOrder::LowFirst] {
            for byte in [ByteOrder::Big, ByteOrder::Little] {
                let context = ParseContext {
                    order: Order { bit, byte },
                    status: InputStatus::Final,
                };
                assert_eq!(
                    parse(1, b"aaa", context, 128, 10_000),
                    Answer::Success(Cursor { byte: 3, bit: 0 }, 3)
                );
            }
        }
        let mut p = Program::new();
        let a: Rule<Number> = p.reserve(Kind::Number);
        let ca = p.call(a);
        let bit = p.literal(1, 1);
        let more = p.seq(ca, bit);
        let body = p.choice(more, bit);
        p.bind(a, body);
        let mut work = Workspace::allocate(1, 1, 100_000, 128, 10_000).unwrap();
        assert_eq!(
            number(run(
                &p,
                &mut work,
                &[0b1110_0000],
                &[],
                a.id,
                Cursor { byte: 0, bit: 0 },
                ParseContext::FINAL
            )),
            Answer::Success(Cursor { byte: 0, bit: 3 }, 3)
        );
    }
}

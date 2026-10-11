//! Standalone controls for borrowed and static metadata return shapes.
#![no_std]

pub struct Label<'a> {
    pub name: &'a str,
}

pub struct Store<'a> {
    pub label: Option<Label<'a>>,
}

pub fn save<'a>(store: &mut Store<'a>, label: Label<'a>) {
    store.label = Some(label);
}

pub fn borrowed(name: &str) -> Store<'_> {
    let mut store = Store { label: None };
    save(&mut store, Label { name });
    store
}

pub fn literal_label() -> Label<'static> {
    Label { name: "tag" }
}

pub fn literal_store() -> Store<'static> {
    borrowed("tag")
}

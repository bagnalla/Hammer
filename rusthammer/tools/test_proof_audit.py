#!/usr/bin/env python3
"""Exercise the compiled auditor with isolated Lean modules, including deliberate failures.

After `lake build proof-audit`, run from lean/ with
`lake env python3 ../tools/test_proof_audit.py`.
"""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


AUDITOR = Path(__file__).resolve().parents[1] / "lean/.lake/build/bin/proof-audit"
LEAN = shutil.which("lean")


class ProofAuditTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="rusthammer-audit-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.env = dict(os.environ)
        self.env["LEAN_PATH"] = str(self.root) + os.pathsep + self.env.get("LEAN_PATH", "")

    def command(self, *args):
        return subprocess.run(args, cwd=self.root, env=self.env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    def module(self, name, code, compile=True):
        source = self.root / (name.replace(".", "/") + ".lean")
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(code)
        if compile:
            # Allow warnings here so the auditor, rather than the compiler, must reject sorryAx.
            result = self.command(LEAN, "-DautoImplicit=false", "-o",
                                  str(source.with_suffix(".olean")), str(source))
            self.assertEqual(result.returncode, 0, result.stdout)

    def audit(self, error=None):
        result = self.command(str(AUDITOR), "AuditFixture")
        if error is None:
            self.assertEqual(result.returncode, 0, result.stdout)
        else:
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn(error, result.stdout)

    def test_standard_axioms_and_private_declarations(self):
        self.module("AuditFixture", """
namespace Elsewhere
private theorem helper : True := True.intro
theorem public_result : True := helper
noncomputable def pick {α : Type} (h : Nonempty α) : α := Classical.choice h
theorem extensionality {p q : Prop} (h : p ↔ q) : p = q := propext h
theorem quotient_sound (a b : Nat) :
    Quot.mk (fun (_ _ : Nat) => True) a = Quot.mk (fun (_ _ : Nat) => True) b :=
  Quot.sound True.intro
end Elsewhere
""")
        self.audit()

    def test_unimported_nested_module_with_unused_private_axiom(self):
        self.module("AuditFixture", "theorem good : True := True.intro\n")
        # New modules need no import in the root; names and visibility do not limit discovery.
        self.module("AuditFixture.Nested.New", """
module
namespace Elsewhere
private axiom unproved : False
end Elsewhere
""")
        self.audit("unproved")

    def test_unused_dependency_axiom_is_outside_project(self):
        self.module("Dependency", "axiom RustHammer.foreign : Nat\n")
        self.module("AuditFixture", "import Dependency\ntheorem good : True := True.intro\n")
        self.audit()

    def test_definition_transitively_using_dependency_axiom(self):
        self.module("Dependency", "axiom assumption : Nat\nnoncomputable def intermediate := assumption\n")
        self.module("AuditFixture", """
import Dependency
namespace Elsewhere
private noncomputable def helper : Nat := intermediate
noncomputable def result : Nat := helper
end Elsewhere
""")
        self.audit("assumption")

    def test_unused_admitted_theorem(self):
        self.module("AuditFixture", "private theorem unproved : False := by sorry\n")
        self.audit("sorryAx")

    def test_missing_sources(self):
        self.audit("No Lean source modules found")

    def test_missing_compiled_module(self):
        self.module("AuditFixture", "theorem good : True := True.intro\n")
        self.module("AuditFixture.New", "theorem new_result : True := True.intro\n", compile=False)
        self.audit("AuditFixture.New")

    def test_empty_development(self):
        self.module("AuditFixture", "import Init\n")
        self.audit("no declarations found")


if __name__ == "__main__":
    unittest.main()

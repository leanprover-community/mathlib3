#!/usr/bin/env python3
from pathlib import Path
from shutil import copy
from tempfile import NamedTemporaryFile, TemporaryDirectory
from textwrap import dedent
import subprocess
import unittest


SCRIPTS_DIR = Path(__file__).parent.resolve()
ROOT_DIR = SCRIPTS_DIR.parent


class TestLinterIntegration(unittest.TestCase):
    def test_path_combinations(self):
        """
        The linter can be run with absolute or relative paths.

        This works both for the executable itself as well as any provided
        files.
        """

        new_file = ROOT_DIR / "src/somenewfile.lean"
        self.assertFalse(new_file.is_file())
        new_file.write_text("example : 2 = 2\n")
        self.addCleanup(new_file.unlink)

        exceptions = SCRIPTS_DIR.joinpath("style-exceptions.txt")
        self.assertTrue(exceptions.is_file)
        self.addCleanup(exceptions.write_text, exceptions.read_text())
        subprocess.run(
            ["./scripts/update-style-exceptions.sh"],
            check=True,
            capture_output=True,
            cwd=ROOT_DIR,
        )

        combinations = [
            (
                ("relative", "./lint-style.py"),
                ("relative", "../src/somenewfile.lean"),
                ("cwd", SCRIPTS_DIR),
            ), (
                ("relative", "./lint-style.py"),
                ("absolute", (ROOT_DIR / "src/somenewfile.lean").resolve()),
                ("cwd", SCRIPTS_DIR),
            ), (
                ("absolute", (SCRIPTS_DIR / "lint-style.py").resolve()),
                ("relative", "../src/somenewfile.lean"),
                ("cwd", SCRIPTS_DIR),
            ), (
                ("absolute", (SCRIPTS_DIR / "lint-style.py").resolve()),
                ("absolute", (ROOT_DIR / "src/somenewfile.lean").resolve()),
                ("cwd", SCRIPTS_DIR),
            ), (
                ("absolute", (SCRIPTS_DIR / "lint-style.py").resolve()),
                ("absolute", (ROOT_DIR / "src/somenewfile.lean").resolve()),
                ("cwd", Path.home()),
            ),
        ]

        for (
            (linter_kind, linter_path),
            (file_kind, file_path),
            (_, cwd),
        ) in combinations:
            with self.subTest(
                linter_kind=linter_kind,
                file_kind=file_kind,
                cwd=cwd,
            ):
                subprocess.run([linter_path, file_path], check=True, cwd=cwd)

    def test_it_fails_for_missing_copyright_headers(self):
        """
        Failing to include a copyright header at the top of a file warns.
        """
        with NamedTemporaryFile(suffix=".lean") as file:
            file.write(b"example : 37 = 37\n")
            file.flush()
            result = subprocess.run(
                [SCRIPTS_DIR / "lint-style.py", file.name],
                capture_output=True,
            )
        self.assertIn(b"ERR_COP", result.stdout)

    def test_reserved_notation_is_allowed_in_reserved_notation(self):
        """
        reserved_notation.lean is the one file that may reserve notation.
        """
        result = subprocess.run(
            [
                SCRIPTS_DIR / "lint-style.py",
                ROOT_DIR / "src/tactic/reserved_notation.lean",
            ],
            check=True,
            capture_output=True,
        )
        self.assertNotIn(b"reserved notation", result.stdout)
        self.assertNotIn(b"reserved notation", result.stderr)
        self.assertNotIn(b"ERR_RNT", result.stdout)
        self.assertNotIn(b"ERR_RNT", result.stderr)

    def test_reserved_notation_is_allowed_in_relative_reserved_notation(self):
        """
        reserved_notation.lean should allow reserving notation even when
        checked via a relative path.
        """
        result = subprocess.run(
            [
                "./scripts/lint-style.py",
                "src/tactic/reserved_notation.lean",
            ],
            capture_output=True,
            cwd=ROOT_DIR,
        )
        self.assertNotIn(b"reserved notation", result.stdout)
        self.assertNotIn(b"reserved notation", result.stderr)
        self.assertNotIn(b"ERR_RNT", result.stdout)
        self.assertNotIn(b"ERR_RNT", result.stderr)

    def test_updating_style_exceptions_uses_relative_paths(self):
        """
        The scripts/update-style-exceptions.sh file updates style exceptions.

        It emits relative paths when doing so, since the file will be synced
        with other remote machines with different filesystems.
        """
        exceptions = SCRIPTS_DIR.joinpath("style-exceptions.txt")
        self.assertTrue(exceptions.is_file)
        current_contents = exceptions.read_text()
        self.assertNotIn(str(ROOT_DIR), current_contents)
        self.addCleanup(exceptions.write_text, current_contents)

        subprocess.run(
            ["./scripts/update-style-exceptions.sh"],
            check=True,
            capture_output=True,
            cwd=ROOT_DIR,
        )
        self.assertNotIn(
            str(ROOT_DIR),
            SCRIPTS_DIR.joinpath("style-exceptions.txt").read_text(),
        )

    def test_running_the_shell_script_does_not_error(self):
        """
        Normally, users will run scripts/lint-style.sh, which will run the
        linter on all files within mathlib.

        Running it exits with successful return code.

        This test will execute in a separate directory tree to make sure
        it doesn't fail if there are current style warnings.
        """

        with TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            for each in "scripts", "src", "archive", "counterexamples":
                root.joinpath(each).mkdir()

            copy(SCRIPTS_DIR / "lint-style.sh", root / "scripts")
            copy(SCRIPTS_DIR / "lint-style.py", root / "scripts")

            # Give us at least one file to check
            root.joinpath("src", "unittesting123.lean").write_text(
                dedent(
                    """\
                    /-
                    Copyright (c) 2021 Someone. All rights reserved.
                    Released under Apache 2.0 license as described in the file LICENSE.
                    Authors: Someone
                    -/
                    example : 37 = 37 := rfl
                    """,
                )
            )

            subprocess.run(["./scripts/lint-style.sh"], check=True, cwd=root)


if __name__ == "__main__":
    unittest.main(verbosity=2)

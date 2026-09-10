"""Integrity boundaries for the external-release attachment; no integrations."""
import hashlib
import io
from pathlib import Path
import tempfile
import unittest
import zipfile

import check_external_numerics as check


class ExternalReleaseTests(unittest.TestCase):
    def test_repository_matches_completed_release_and_lean_targets(self):
        check.check_repository()

    def test_changed_lean_target_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "research").mkdir()
            (root / check.DATA).symlink_to(check.ROOT / check.DATA, target_is_directory=True)
            (root / "formal").mkdir()
            for path in (check.ROOT / "formal").glob("*.lean"):
                (root / "formal" / path.name).symlink_to(path)
            changed = root / "formal/SourceData182.lean"
            changed.unlink()
            changed.write_text("-- changed numerical target\n")
            with self.assertRaisesRegex(ValueError, "Lean numerical target differs"):
                check.check_repository(root)

    def test_unsafe_archive_paths_are_rejected(self):
        for name in ("../x", "/x", "a/../../x", "a\\x", "", "a//b", "./x"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                check.safe_relative(name)

    def test_corrupted_download_is_rejected_before_opening_zip(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "asset.zip"
            path.write_bytes(b"bad")
            asset = {"archive": {"bytes": 3, "sha256": "0" * 64}}
            with self.assertRaisesRegex(ValueError, "Archive SHA256 differs"):
                check.check_archive(path, asset, {})

    def test_unlisted_zip_member_is_rejected_even_with_matching_outer_hash(self):
        buffer = io.BytesIO()
        with zipfile.ZipFile(buffer, "w") as archive:
            archive.writestr("bundle/extra", b"unlisted")
        payload = buffer.getvalue()
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "asset.zip"
            path.write_bytes(payload)
            asset = {"archive": {"bytes": len(payload), "root": "bundle",
                                  "sha256": hashlib.sha256(payload).hexdigest(),
                                  "manifest_sha256": "0" * 64}}
            with self.assertRaisesRegex(ValueError, "missing, extra, or duplicate"):
                check.check_archive(path, asset, {"files": {}})


if __name__ == "__main__":
    unittest.main()

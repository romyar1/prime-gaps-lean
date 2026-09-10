# Updating the existing GitHub project

Use the existing **[romyar1/prime-gaps-lean](https://github.com/romyar1/prime-gaps-lean)**
repository. The numerical update is distributed with the
[external-numerics-20260909 release](https://github.com/romyar1/prime-gaps-lean/releases/tag/external-numerics-20260909).
The following records the source-update and release workflow.

## Source update

1. In GitHub Desktop, open or clone `romyar1/prime-gaps-lean`, fetch the latest
   changes, and start a branch such as `numerical-package-20260909`. Use a clean
   clone separate from ongoing Lean research.
2. Extract the updated **source** ZIP. Copy the contents of its `prime-gaps-lean/`
   folder into the clone, including hidden files such as `.github` and
   `.gitattributes`. Command–Shift–period reveals hidden files on macOS.
   Do not copy Git history or any build cache.
3. Review the changes. The base is commit
   `78e052bd50e64a34f58866b8b306844b72926c60`. Changes should be documentation,
   numerical verifier/evidence files, integrity tests and workflow, and packaging
   rules. There should be no changes to `formal/`, existing numerical inputs,
   dependency pins, or the Lean verifier. If the remote has advanced, apply the
   accompanying patch to the new head instead of overwriting newer files, and
   review any conflicts.
4. Run the inexpensive local checks from the repository root:

   ```sh
   python3 -B scripts/check_external_numerics.py
   python3 -B provenance/check_data.py
   python3 -B -m unittest discover -s scripts -p 'test_*.py'
   ```

5. Commit with a summary such as `Add verified external numerical package and evidence`.
   Push the branch to this same repository, review the diff and checks, and
   merge when ready. The existing Lean workflow and new numerical integrity
   workflow have different scopes; neither makes the theorem unconditional.
   The numerical integrity workflow does not rerun the integrals.

The extracted source files belong in Git. Uploading only the source ZIP as a
repository file would not update the individual sources or workflow.

## Numerical release attachment

The 244,843,318-byte numerical bundle goes in a **GitHub Release**. GitHub blocks
ordinary Git files over 100 MiB and browser uploads over 25 MiB, and recommends
releases for large binaries. See
[GitHub's large-file documentation](https://docs.github.com/en/repositories/working-with-files/managing-large-files/about-large-files-on-github).

1. Open [Releases for this repository](https://github.com/romyar1/prime-gaps-lean/releases)
   and prepare a release targeting the merged source-update commit. The suggested
   new tag is `external-numerics-20260909`.
2. Use the title **External numerical verification for the conditional 182 development**
   and the prepared [release notes](release-notes-external-numerics-20260909.md).
   Preserve the proof limitations. When pasting into the release editor, turn
   relative documentation links into links to those files at the release tag.
3. Attach `prime-gaps-external-182-verified-20260909.zip` and its `.zip.sha256`
   companion. Check the name, size and SHA256 against
   [asset.json](../research/numerical_182/asset.json).
4. Review the draft and publish when ready. After publication, replace the
   prepared/unpublished wording in the numerical guide with the actual release
   link. Keep future corrections in this same repository.

The numerical archive contains its own licenses, original provenance and
reproduction instructions. Keep it byte-for-byte unchanged so the recorded
SHA256 and acceptance receipt retain their meaning.

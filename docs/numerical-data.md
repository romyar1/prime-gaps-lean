# Numerical data and provenance

[`inputs/source_certificates`](../inputs/source_certificates/) contains the
16 JSON files used as the source-certificate input collection for the 182
analytic development. They include the fixed trial, the aggregate certificate,
and the cap/source component records. Every numerical value, rational or
interval string, count, bound, warning, and embedded digest is preserved.

These files support the 262 integral inequalities listed in
[`assumptions.md`](assumptions.md). They do not discharge those Lean premises.
The original 16-record collection is supplemented by the
[completed external numerical package](../research/numerical_182/README.md).
Its full rerun passed all 262 target comparisons on 9 September 2026, with
14 implementation audits and four deliberate rejection tests. The source
repository includes the verifier drivers and compact evidence; the pinned
release attachment includes all source programs, arrays, runtime libraries,
fresh production outputs and full receipts. Its tested numerical runtime is
Apple Silicon macOS, Python 3.12 and NumPy 2.3.5.

Rebuilding Lean does not rerun those integrations or convert JSON records into
kernel-checked proofs. The original `provenance/check_data.py` remains a
collection-integrity and path-normalization check; it performs no integration.
Use the external package's production and acceptance commands for a new run.
Its acceptance receipt covers all 262 comparisons, including both bounds for
each of the 60 outer components and the 137 inner components.

The full archive preserves original bytes and embedded dependency hashes.
These existing normalized repository records remain unchanged. The external
verification does not alter their provenance or remove the remaining
mathematical review of the algorithms and their connection to the integrals.

## Portable source identifiers

The original records included absolute paths belonging to the producing
machine. Their JSON keys and string values now use the logical identifier
`prime_gaps_20260903/<relative-source-name>`. Only the absolute prefix before
that source-bundle name was removed. This replacement preserves the remaining
bytes, including all number spellings and formatting. Original files remain
untouched.

These logical identifiers are **provenance labels, not working filesystem
paths**. The `source_references` table in
[`data_manifest.json`](../provenance/data_manifest.json) identifies references
whose normalized copies are included, and explicitly marks all other
references `provenance_only_not_in_repository`.

Embedded `trial_sha256`, `input_sha256`, and similar fields continue to identify
the original source bytes. They have not been rewritten to describe the
normalized copies. For each included file the manifest separately records:

- the SHA256 and size of the original bytes;
- the SHA256 and size of the published bytes;
- the number and JSON locations of changed path keys and values;
- a canonical hash of every non-path scalar, including numerical tokens and
  all rational/interval strings;
- whether normalization left that entire non-path payload unchanged.

Thus an original embedded digest may differ from the digest of the included
normalized copy. Use the manifest's `published_sha256` to verify the copy.

## Check the collection

From the repository root, with Python 3.10 or later:

```sh
python3 provenance/check_data.py
```

This checks each published file's bytes and canonical payload, the reference
inventory, and the absence of absolute host paths. To compare against an
available original input collection as well:

```sh
python3 provenance/check_data.py --source-dir /path/to/original/source_certificates
```

The second form is read-only. It additionally checks the original hashes and
the exact metadata-only normalization for every file. Neither form is an
interval-arithmetic recomputation or a Lean proof.

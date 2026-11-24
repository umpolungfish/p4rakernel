# Measurement export handoff

`G-mOMonadOS` exposes `abc stream --json`, and
`scripts/abc_json_to_certificate_manifest.py` validates that artifact before
handing its cutoffs and attained triples to the exact Lean certificate
generator. The converter rejects malformed triples, non-monotone cutoffs, and
failed calibration flags. It never turns floating-point measurements into
proof terms.

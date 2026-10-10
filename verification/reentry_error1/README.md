# Re-entry compilation and native storage controls

Completed checks:

- `cmake --build build/stage1 -j 4`: exit 0. The complete output is in
  `reentry_error1_fix.log`.
- `build/stage1/bin/lean tests/lean/run/reentryValue.lean`: exit 0. Its empty
  output is in `reentry_value_control.log`. The control checks all 16
  membership masks, expression construction, metadata, native environment
  insertion and lookup. Native insertion uses `doCheck := false` to isolate
  the storage ABI.


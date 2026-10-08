# Reproducing BongTheory

Prerequisites are Git and Elan. The checked-in `lean-toolchain` selects Lean
4.32.1, and `lake-manifest.json` records the resolved dependency commits after
`lake update`.

```text
git clone https://github.com/hzldew-git/BongTheory.git
cd BongTheory
lake exe cache get
lake build
lake env lean BongTest/CoreAxiomGate.lean
```

For release acceptance, run the commands in a fresh clone on Ubuntu and
Windows and require a clean working tree afterwards.

On a memory-constrained host, a broad Lake build may report a process-level
allocation failure. Re-run the named failed module by itself, then repeat the
aggregate target. Record resource failures separately from Lean elaboration or
kernel errors.

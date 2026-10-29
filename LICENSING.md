# Licensing

This repository uses a split licensing model: the engine is source-available under the Business Source License 1.1, and
the examples, documentation and emitted certificates are open.

## The Telperion engine: Business Source License 1.1

The engine is licensed under the [Business Source License 1.1](LICENSE). The engine means everything in this repository
that is not listed under the open part below: the package in `src/telperion/` (the certificate-emission engine, the
emitters, the CLI, the MCP server and the missions framework), the tests in `tests/`, the tooling in `scripts/` and
`missions/`, the CI in `.github/`, and the packaging files.

- **Free for research.** Academic research, teaching, scholarly publication, personal experimentation and evaluation are
  permitted outright by the Additional Use Grant.
- **Commercial production use** requires a license from the Licensor.
- **Change License:** each release converts to the Apache License 2.0 three years after its release date.
- **Emitted certificates are yours.** Lean files produced by running Telperion are excluded from the Licensed Work; the
  Licensor claims no rights over them.

## The open part: Apache-2.0 / CC-BY-4.0

- The examples in `examples/`, and the documentation in `docs/`, are licensed under the
  [Apache License 2.0](LICENSE-APACHE) for code (generators, scripts, Lean sources) and under
  [CC-BY-4.0](https://creativecommons.org/licenses/by/4.0/) for documents (READMEs, notes, write-ups).
- Emitted certificates (every `.lean` file a generator writes, and every `frozen/` record) are part of the open
  mathematical record and are Apache-2.0, not BSL.

Reviewers do not need any license beyond the Additional Use Grant to regenerate and check every certificate in this
repository.

## Third-party code

`examples/hermitian_moment/lean/` is a verbatim port (see
[`PORT_NOTES.md`](examples/hermitian_moment/lean/PORT_NOTES.md)) of the linear-algebra core from
the public repository [anthropics/zeta-23-lean](https://github.com/anthropics/zeta-23-lean). Those
files are Copyright (c) 2026 Anthropic, PBC, licensed under Apache-2.0, and keep their original
copyright and SPDX headers. The only edit to their bodies is the import-path rename
(`Zeta23.LinAlg.X` → `RHLinalg.X`) that `PORT_NOTES.md` documents; every statement and proof body
is otherwise byte-for-byte identical to the source.

Those headers say "the file LICENSE" — for these files that means
[`examples/hermitian_moment/lean/LICENSE`](examples/hermitian_moment/lean/LICENSE), a byte-identical
copy of this repository's [`LICENSE-APACHE`](LICENSE-APACHE), placed alongside them for that reason.

## History

Telperion was developed inside the public repository [Arda](https://github.com/DrMurphyIsIn/Arda) before it moved here.
Snapshots of it published inside Arda before 2026-08-21 were released entirely under Apache-2.0, and that grant is
irrevocable for those snapshots. The BSL applies to later versions of the engine, including everything in this
repository's history from 2026-08-21 on.

## Contributing

To keep the split licensing model sound, the Licensor must retain full copyright in the engine. Contributions to the
engine therefore require the individual Contributor License Agreement in [`CLA.md`](CLA.md). Contributions to the open
part (`examples/`, `docs/`) need only the usual Apache-2.0 inbound = outbound understanding, with no CLA.

*This document describes intent and is not legal advice.*

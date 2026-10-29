"""Run the Telperion CLI as ``python -m telperion`` (mirrors the ``telperion``
console script in pyproject.toml's [project.scripts])."""

from telperion.cli import main

raise SystemExit(main())

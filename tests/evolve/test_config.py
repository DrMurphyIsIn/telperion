import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.evolve.config import EvolveConfig


def test_default_config_is_sane():
    cfg = EvolveConfig.default()
    assert cfg.islands >= 1
    assert cfg.gens >= 1
    assert cfg.use_llm in (True, False)
    assert cfg.lean_project.endswith("g1_floors/lean")
    assert len(cfg.temperatures) >= 1


def test_from_toml_reads_evolve_table(tmp_path):
    p = tmp_path / "t.toml"
    p.write_text(
        "[evolve]\n"
        'model_tag = "qwen2.5-coder:7b"\n'
        "islands = 3\n"
        "gens = 20\n"
        "temperatures = [0.2, 0.6, 1.0]\n"
    )
    cfg = EvolveConfig.from_toml(str(p))
    assert cfg.model_tag == "qwen2.5-coder:7b"
    assert cfg.islands == 3
    assert cfg.temperatures == (0.2, 0.6, 1.0)

from telperion.evolve.cli import run_evolve


def test_cli_no_llm_reaches_certifying_champion(capsys):
    rc = run_evolve(["--no-llm", "--islands", "2", "--gens", "8", "--seed", "0"])
    out = capsys.readouterr().out
    assert rc == 0
    assert "CERTIFIES" in out or "champion" in out.lower()

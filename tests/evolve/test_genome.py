from telperion.evolve.genome import (
    UnimodalGenome,
    to_certificate,
    to_prompt_repr,
    from_llm_text,
    complexity,
    NEAR_STAR_Q,
)


def test_greenoracle_builds():
    g = UnimodalGenome(ratio_src=NEAR_STAR_Q, s0=5, lift_max=4)
    cert, art = to_certificate(g)
    assert cert is not None
    assert int(cert.s_star) == 5
    assert art == {}


def test_nondecreasing_ratio_fails_with_artifact():
    g = UnimodalGenome(ratio_src="(2*s+1)/(2*s+3)", s0=3, lift_max=4)
    cert, art = to_certificate(g)
    assert cert is None
    assert "error" in art and len(art["error"]) > 0


def test_prompt_roundtrip():
    g = UnimodalGenome(ratio_src=NEAR_STAR_Q, s0=5, lift_max=4)
    back = from_llm_text(to_prompt_repr(g))
    assert back == g


def test_from_llm_text_is_total_on_garbage():
    assert from_llm_text("not json at all {{{") is None
    assert from_llm_text('{"ratio_src": "s+", "s0": "oops"}') is None


def test_complexity_prefers_smaller():
    assert complexity(UnimodalGenome(NEAR_STAR_Q, 5, 2)) < complexity(UnimodalGenome(NEAR_STAR_Q, 9, 4))

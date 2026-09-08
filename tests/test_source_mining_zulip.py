"""Lean-Zulip adapter — offline unit tests (no network, no credentials).

Exercises the pure message parser (HTML stripping + entity unescape, id/title
shape, near-message permalink), confirms an RH-relevant topic classifies through
the shared core, and confirms the credential-less fetch degrades to a graceful
no-op (returns [] rather than raising or hitting the network).
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.palomar_mine import classify_entry  # noqa: E402
from telperion.source_mining_zulip import (  # noqa: E402
    ZULIP_SITE,
    fetch_zulip,
    parse_zulip_messages,
)

# A Zulip /api/v1/messages payload: one RH-relevant topic (with an HTML tag and a
# &quot; entity to exercise stripping/unescape), one off-topic.
PAYLOAD = {
    "messages": [
        {
            "id": 42,
            "subject": "Li's criterion",
            "content": "<p>Is the Riemann zeta function's completed xi "
                       "&quot;Li-Keiper&quot; positivity ladder formalized? "
                       "RiemannHypothesis holds iff every coefficient is "
                       "nonnegative.</p>",
            "sender_full_name": "A. Mathematician",
            "timestamp": 1757000000,
            "stream_id": 7,
        },
        {
            "id": 43,
            "subject": "coffee thread",
            "content": "<p>Anyone tried the new espresso place downtown?</p>",
            "sender_full_name": "B. Coder",
            "timestamp": 1757000100,
            "stream_id": 7,
        },
    ],
}


def test_parse_extracts_id_title_and_stripped_abstract():
    entries = parse_zulip_messages(PAYLOAD, stream="Palomar")
    assert len(entries) == 2
    e0 = entries[0]
    assert e0["id"] == "zulip-42"
    assert e0["title"] == "Li's criterion"
    # HTML tags gone, &quot; unescaped to ", whitespace collapsed.
    assert "<p>" not in e0["abstract"] and "</p>" not in e0["abstract"]
    assert '"Li-Keiper"' in e0["abstract"]
    assert "&quot;" not in e0["abstract"]
    assert e0["abstract"].startswith("Is the Riemann zeta")
    # near-message permalink carries the stream + message id.
    assert e0["source"]["url"] == f"{ZULIP_SITE}/#narrow/stream/Palomar/near/42"


def test_rh_message_classifies_through_the_core():
    e0 = parse_zulip_messages(PAYLOAD, stream="Palomar")[0]
    c = classify_entry(e0)
    assert c is not None
    assert "rh" in c.topics


def test_off_topic_message_does_not_classify():
    e1 = parse_zulip_messages(PAYLOAD, stream="Palomar")[1]
    assert classify_entry(e1) is None


def test_fetch_is_graceful_noop_without_credentials(monkeypatch):
    # No creds via args and none in the environment -> must return [] (no raise,
    # no network) so an unprovisioned bot degrades to "no leads".
    monkeypatch.delenv("ZULIP_EMAIL", raising=False)
    monkeypatch.delenv("ZULIP_API_KEY", raising=False)
    monkeypatch.delenv("ZULIP_SITE", raising=False)
    assert fetch_zulip(email=None, api_key=None) == []


def test_parse_handles_empty_payload():
    assert parse_zulip_messages({}) == []
    assert parse_zulip_messages({"messages": []}) == []

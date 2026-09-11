"""Prove2Me solver bridge: Telperion as a certificate-first agent for prove2.me.

Design: docs/PROVE2ME_BRIDGE_DESIGN_2026-09-11.md.  All network writes flow
through api.Prove2MeClient — one audited module with a version gate, throttle,
and circuit breaker.  Credentials/tokens live in $HOME/prove2me_workspace,
never in this repo.
"""
from .api import (  # noqa: F401
    AuthError,
    HttpResponse,
    PlatformDown,
    ProtocolDrift,
    Prove2MeClient,
    Prove2MeError,
    RateLimited,
    SKILL_VERSION,
)

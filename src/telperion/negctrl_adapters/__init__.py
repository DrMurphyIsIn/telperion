"""Negative-control adapters: importing this package registers every adapter."""
from __future__ import annotations

from . import adapter_c_g_round  # noqa: F401
from . import adapter_cone_farkas  # noqa: F401
from . import adapter_consequence  # noqa: F401
from . import adapter_constrained_s_o_s  # noqa: F401
from . import adapter_exact_fact  # noqa: F401
from . import adapter_fwd_telescope  # noqa: F401
from . import adapter_handelman  # noqa: F401
from . import adapter_identity  # noqa: F401
from . import adapter_infeasibility  # noqa: F401
from . import adapter_nullstellensatz  # noqa: F401
from . import adapter_rational_identity  # noqa: F401
from . import adapter_rational_s_o_s  # noqa: F401
from . import adapter_real_nullstellensatz  # noqa: F401
from . import adapter_s_o_s  # noqa: F401
from . import adapter_s_o_s_refutation  # noqa: F401
from . import adapter_telescoping_potential  # noqa: F401
from . import adapter_w_z  # noqa: F401
from . import adapter_zero_free_cosine  # noqa: F401

__all__ = ['adapter_c_g_round', 'adapter_cone_farkas', 'adapter_consequence', 'adapter_constrained_s_o_s', 'adapter_exact_fact', 'adapter_fwd_telescope', 'adapter_handelman', 'adapter_identity', 'adapter_infeasibility', 'adapter_nullstellensatz', 'adapter_rational_identity', 'adapter_rational_s_o_s', 'adapter_real_nullstellensatz', 'adapter_s_o_s', 'adapter_s_o_s_refutation', 'adapter_telescoping_potential', 'adapter_w_z', 'adapter_zero_free_cosine']

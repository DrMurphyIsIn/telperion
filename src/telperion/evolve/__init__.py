"""Evolutionary certificate search over Telperion families.

Proposes certificate programs; the untrusted-by-design generator's output still
passes the identical certify/emit/lake-build gate. Nothing here is auto-frozen.
"""
from .config import EvolveConfig

__all__ = ["EvolveConfig"]

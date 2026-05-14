-- Top-level module for ocapn-lean.
--
-- Submodules:
--   * `OcapnLean.Model`           — abstract OCapN data model
--   * `OcapnLean.Captp.Messages`  — algebraic types for op:* and desc:*
--   * `OcapnLean.Captp.Spec`      — Veil module: single-peer CapTP spec

import OcapnLean.Model
import OcapnLean.Captp.Messages
import OcapnLean.Captp.Spec
import OcapnLean.Captp.Twoparty
import OcapnLean.Captp.CrossedHellos
import OcapnLean.Captp.Gc
import OcapnLean.Captp.NoForgery

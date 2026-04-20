import Std.Data.HashMap
import VersoManual
import SystemsProposal

open Verso Doc
open Verso.Genre Manual

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1

def main := manualMain (%doc SystemsProposal) (config := config)

import BinaryCollatz

/-!
# Collatz Cycles Analysis - Main Entry Point

This is the main entry point for the Collatz cycles analysis project.
-/

def main : IO Unit := do
  IO.println "Collatz Cycles Analysis"
  IO.println "======================"
  IO.println ""
  IO.println "This project contains the Lean formalization of the proof that"
  IO.println "binary Collatz cycles cannot exist."
  IO.println ""
  IO.println "Main theorem: binary_collatz_cycles_impossible"
  IO.println "  For all k > 0, no k-cycle exists in the binary Collatz function."
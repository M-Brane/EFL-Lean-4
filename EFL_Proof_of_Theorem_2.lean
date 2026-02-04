-- EFL_Proof_of_Theorem_2_v7.lean
-- VERSION MARKER: v7
--
-- Fix vs v6:
--   * Break a long line (>100 chars) in the `hv''` definition inside
--     `candidates_rule2_first_subset_rule1` to satisfy the linter.

import Mathlib
import EFLLean.EFL_Definitions
import EFLLean.EFL_Lemmas_for_Theorem_2

namespace EFL

section Theorem2

variable {n : Nat} (G : EFLGraph n)

local instance : DecidableEq G.vertices := G.dec_eq

/-- Baseline candidate pool at a single construction step. -/
noncomputable def candidates_baseline
    (i : Fin n) (excluded : Finset G.vertices) (built : Fin n → Option G.vertices) :
    Finset G.vertices :=
  available_consistent_vertices G i excluded built

/-- Rule 1 candidate pool: try non-free first when possible, else free. -/
noncomputable def candidates_rule1
    (i : Fin n) (excluded : Finset G.vertices) (built : Fin n → Option G.vertices) :
    Finset G.vertices :=
  let nf := non_free_available G i excluded built
  if nf.Nonempty then nf else free_available G i excluded built

/--
Given a nonempty candidate pool, the subset of candidates of maximal degree
(“tested first” under Rule 2).
-/
noncomputable def max_degree_candidates
    (cands : Finset G.vertices) (hc : cands.Nonempty) :
    Finset G.vertices := by
  classical
  let ds : Finset Nat := cands.image (vertex_degree G)
  have hds : ds.Nonempty := by
    rcases hc with ⟨v, hv⟩
    refine ⟨vertex_degree G v, ?_⟩
    exact Finset.mem_image.2 ⟨v, hv, rfl⟩
  let m : Nat := ds.max' hds
  exact cands.filter (fun v => vertex_degree G v = m)

/-- Rule 2 "first-try" pool. -/
noncomputable def candidates_rule2_first
    (i : Fin n) (excluded : Finset G.vertices) (built : Fin n → Option G.vertices) :
    Finset G.vertices := by
  classical
  let nf := non_free_available G i excluded built
  by_cases hnf : nf.Nonempty
  · exact max_degree_candidates (G := G) nf hnf
  · exact free_available G i excluded built

/-- Rule 1 candidates are a subset of baseline candidates. -/
lemma candidates_rule1_subset_baseline
    (i : Fin n) (excluded : Finset G.vertices) (built : Fin n → Option G.vertices) :
    candidates_rule1 (G := G) i excluded built
      ⊆ candidates_baseline (G := G) i excluded built := by
  classical
  intro v hv
  dsimp [candidates_baseline] at *
  set nf : Finset G.vertices := non_free_available G i excluded built
  by_cases hnf : nf.Nonempty
  · have hv' : v ∈ non_free_available G i excluded built := by
      simpa [candidates_rule1, nf, hnf] using hv
    have hv'' :
        v ∈ available_consistent_vertices G i excluded built ∧
          1 < vertex_degree G v := by
      simpa [non_free_available] using hv'
    exact hv''.1
  · have hv' : v ∈ free_available G i excluded built := by
      simpa [candidates_rule1, nf, hnf] using hv
    have hv'' :
        v ∈ available_consistent_vertices G i excluded built ∧
          vertex_degree G v = 1 := by
      simpa [free_available] using hv'
    exact hv''.1

/-- Rule 2 "first-try" candidates are a subset of Rule 1 candidates. -/
lemma candidates_rule2_first_subset_rule1
    (i : Fin n) (excluded : Finset G.vertices) (built : Fin n → Option G.vertices) :
    candidates_rule2_first (G := G) i excluded built
      ⊆ candidates_rule1 (G := G) i excluded built := by
  classical
  intro v hv
  set nf : Finset G.vertices := non_free_available G i excluded built
  by_cases hnf : nf.Nonempty
  · have hv' : v ∈ max_degree_candidates (G := G) nf hnf := by
      simpa [candidates_rule2_first, nf, hnf] using hv
    have hv'' :
        v ∈ nf ∧
          vertex_degree G v =
            (nf.image (vertex_degree G)).max'
              (by
                rcases hnf with ⟨x, hx⟩
                refine ⟨vertex_degree G x, ?_⟩
                exact Finset.mem_image.2 ⟨x, hx, rfl⟩) := by
      simpa [max_degree_candidates] using hv'
    have : v ∈ nf := hv''.1
    simpa [candidates_rule1, nf, hnf] using this
  · have hv' : v ∈ free_available G i excluded built := by
      simpa [candidates_rule2_first, nf, hnf] using hv
    simpa [candidates_rule1, nf, hnf] using hv'

/-- Rule 1 tries no more first-step candidates than baseline. -/
theorem rule1_reduces_or_equals_first_step_candidates
    (i : Fin n) (excluded : Finset G.vertices) (built : Fin n → Option G.vertices) :
    (candidates_rule1 (G := G) i excluded built).card
      ≤ (candidates_baseline (G := G) i excluded built).card := by
  classical
  exact Finset.card_le_card
    (candidates_rule1_subset_baseline (G := G) i excluded built)

/-- Rule 2 further prunes the first-step candidates compared to Rule 1. -/
theorem rule2_reduces_or_equals_first_step_candidates
    (i : Fin n) (excluded : Finset G.vertices) (built : Fin n → Option G.vertices) :
    (candidates_rule2_first (G := G) i excluded built).card
      ≤ (candidates_rule1 (G := G) i excluded built).card := by
  classical
  exact Finset.card_le_card
    (candidates_rule2_first_subset_rule1 (G := G) i excluded built)

/-- Combined inequality: Rule 2 (with Rule 1) prunes at least as much as baseline. -/
theorem theorem_2_relative_efficiency_first_step
    (i : Fin n) (excluded : Finset G.vertices) (built : Fin n → Option G.vertices) :
    (candidates_rule2_first (G := G) i excluded built).card
      ≤ (candidates_baseline (G := G) i excluded built).card := by
  classical
  calc
    (candidates_rule2_first (G := G) i excluded built).card
        ≤ (candidates_rule1 (G := G) i excluded built).card := by
          exact rule2_reduces_or_equals_first_step_candidates (G := G) i excluded built
    _ ≤ (candidates_baseline (G := G) i excluded built).card := by
          exact rule1_reduces_or_equals_first_step_candidates (G := G) i excluded built

end Theorem2

end EFL

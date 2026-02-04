-- EFL_Lemmas_for_Theorem_2_v9h.lean
-- VERSION MARKER: v9h
--
-- Fixes vs v9g:
--   * Fix linter `style.cdot` at the `refine ⟨?_, ?_, ?_⟩` block by merging the isolated `·`
--     with the following line.

import Mathlib
import EFLLean.EFL_Definitions

namespace EFL

section Theorem2Rules

variable {n : Nat} (G : EFLGraph n)

local instance : DecidableEq G.vertices := G.dec_eq

/-- Rule 1 selector (Free-Vertex-Last): try non-free candidates first; else try free. -/
noncomputable def select_candidate
    (i : Fin n) (excluded : Finset G.vertices)
    (built : Fin n → Option G.vertices) : Option G.vertices := by
  classical
  let nf := non_free_available G i excluded built
  exact
    if hnf : (∃ x, x ∈ nf) then
      some (Classical.choose hnf)
    else
      let fr := free_available G i excluded built
      if hfr : (∃ x, x ∈ fr) then
        some (Classical.choose hfr)
      else
        none

/--
Rule 1 lemma:
If `select_candidate` returns a free vertex, then there were no non-free candidates.
-/
lemma select_candidate_free_implies_no_nonfree
    (i : Fin n) (excluded : Finset G.vertices)
    (built : Fin n → Option G.vertices) (v : G.vertices)
    (hsel : select_candidate G i excluded built = some v)
    (hfree : is_free G v) :
    non_free_available G i excluded built = ∅ := by
  classical
  unfold select_candidate at hsel
  set nf : Finset G.vertices := non_free_available G i excluded built
  by_cases hnf : (∃ x, x ∈ nf)
  · have hv : Classical.choose hnf = v := by
      simpa [nf, hnf] using hsel

    have hmem : Classical.choose hnf ∈ nf := Classical.choose_spec hnf

    have hv_deg : 1 < vertex_degree G v := by
      have : Classical.choose hnf ∈ available_consistent_vertices G i excluded built ∧
          1 < vertex_degree G (Classical.choose hnf) := by
        simpa [nf, non_free_available] using hmem
      simpa [hv] using this.2

    have : degree G v ≠ 1 := by
      have : degree G v > 1 := by
        simpa [degree] using hv_deg
      exact ne_of_gt this

    exact (this hfree).elim
  · have hn0 : nf = ∅ := (Finset.not_nonempty_iff_eq_empty).1 hnf
    simp [nf, hn0]

/-!
### Rule 2 (Fewest-Hyperedges-Last)
-/

/-- Local Rule 2 condition: chosen maximizes `vertex_degree` among `cands`. -/
def follows_rule_2_local (cands : Finset G.vertices) (chosen : G.vertices) : Prop :=
  chosen ∈ cands ∧ (1 < vertex_degree G chosen) ∧
    ∀ v ∈ cands, 1 < vertex_degree G v → vertex_degree G v ≤ vertex_degree G chosen

/--
Rule-2-aware selector:
If the non-free pool is nonempty, pick a max-degree element; otherwise fall back to Rule 1 selector.
-/
noncomputable def select_candidate_rule2
    (i : Fin n) (excluded : Finset G.vertices)
    (built : Fin n → Option G.vertices) : Option G.vertices := by
  classical
  let nf := non_free_available G i excluded built
  exact
    if hnf : nf.Nonempty then
      let m : G.vertices := Classical.choose (Finset.exists_max_image nf (vertex_degree G) hnf)
      some m
    else
      select_candidate G i excluded built

/--
Rule 2 guarantee (nonempty case):
If the non-free pool is nonempty and `select_candidate_rule2` returns `v`,
then `v` satisfies the local Rule 2 condition on that pool.
-/
lemma select_candidate_rule2_satisfies_local_rule2_of_nonempty
    (i : Fin n) (excluded : Finset G.vertices)
    (built : Fin n → Option G.vertices) (v : G.vertices)
    (hnf : (non_free_available G i excluded built).Nonempty)
    (hsel : select_candidate_rule2 G i excluded built = some v) :
    follows_rule_2_local G (non_free_available G i excluded built) v := by
  classical
  unfold select_candidate_rule2 at hsel
  set nf : Finset G.vertices := non_free_available G i excluded built

  let m : G.vertices :=
    Classical.choose (Finset.exists_max_image nf (vertex_degree G) (by simpa [nf] using hnf))

  have hm_spec :
      m ∈ nf ∧ ∀ x ∈ nf, vertex_degree G x ≤ vertex_degree G m := by
    simpa [m] using
      (Classical.choose_spec
        (Finset.exists_max_image nf (vertex_degree G) (by simpa [nf] using hnf)))

  have hm_mem : m ∈ nf := hm_spec.1
  have hm_max : ∀ x ∈ nf, vertex_degree G x ≤ vertex_degree G m := hm_spec.2

  have hv : m = v := by
    simpa [nf, hnf, m] using hsel

  subst hv
  refine ⟨?_, ?_, ?_⟩
  · simpa [nf] using hm_mem
  · have : m ∈ available_consistent_vertices G i excluded built ∧ 1 < vertex_degree G m := by
      simpa [nf, non_free_available] using hm_mem
    exact this.2
  · intro w hw hwdeg
    have hw' : w ∈ nf := by simpa [nf] using hw
    exact hm_max w hw'

end Theorem2Rules

end EFL

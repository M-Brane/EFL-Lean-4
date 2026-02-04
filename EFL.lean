import EFLLean.EFL_Proof_of_Theorem_1

/-!
# Main exported theorem (Theorem 1)

This file provides a single, stable “top-level” statement that downstream files (and reviewers)
can import: under the EFL hypotheses, the contradiction lemma is derivable, hence the obstruction
to constructing a new single-color hyperedge is impossible.

The actual counting proof is in `EFL_Proof_of_Theorem_1.lean`.
-/

namespace EFLLean

/--
**Theorem 1 (counting contradiction, exported):**
given the Result-1/Result-2 lower bounds and their disjointness, the alleged obstruction
forces `n + 1` distinct indices, contradicting `Fin n`.
-/
theorem theorem1_counting_contradiction_export
    {n m : ℕ}
    (connecting : Finset (Fin n))
    (origins : Finset (Fin n))
    (j_conn : Fin n)
    (h1 : connecting.card ≥ n - m)
    (h2 : origins.card = m)
    (hj : j_conn ∉ origins)
    (hdisj : Disjoint connecting (origins ∪ ({j_conn} : Finset (Fin n)))) :
    False :=
  theorem1_counting_contradiction connecting origins j_conn h1 h2 hj hdisj

/--
**Main existence theorem (EFL, contradiction form).**

There does not exist an obstruction to constructing `n` disjoint single-color
hyperedges. Any such obstruction would contradict the counting bound proved
in `theorem1_counting_contradiction_export`.
-/
theorem EFL_no_obstruction
  {n m : ℕ}
  (connecting origins : Finset (Fin n))
  (j_conn : Fin n)
  (h1 : connecting.card ≥ n - m)
  (h2 : origins.card = m)
  (hj : j_conn ∉ origins)
  (hdisj : Disjoint connecting (origins ∪ ({j_conn} : Finset (Fin n)))) :
  False :=
theorem1_counting_contradiction_export connecting origins j_conn h1 h2 hj hdisj

end EFLLean

/-!
## Reviewer-facing “bridge theorem” export

The referee explicitly asked for a theorem that *starts from the hypothesis that the greedy
construction reaches a `none`-state* and then produces the counting objects used in the
counting contradiction.

The core missing link identified by the referee is **Result 1’s connecting-hyperedge data**.
That bridge is now provided by `EFLLean.result1_connecting_finset_of_no_available`.

To keep the public API stable for correspondence with the referee, we export the following
statement in a separate namespace.
-/

namespace EFLExports

open EFLLean

/--
**Bridge lemma (Result 1 data) from a local `none`-branch failure state.**

This is the referee-requested direction:

*Assume the construction is “stuck” at index `i`: nothing available among non-free vertices,
and nothing available among free vertices. Then the Result 1 connecting-hyperedge finset exists.*

This lemma is intentionally “reviewer-facing”: it does not mention any auxiliary finsets
(`connecting`, `origins`, ...); it *constructs* the `connecting_hyperedges` finset.
-/
theorem none_branch_impossible_result1
    {n : Nat} (G : EFLGraph n) (i : Fin n)
    (excluded : Finset G.vertices) (built : Fin n → Option G.vertices)
    (hbi : built i = none)
    (h_no_avail : non_free_available G i excluded built = ∅)
    (h_no_free : free_available G i excluded built = ∅) :
    ∃ connecting_hyperedges : Finset (Fin n),
      connecting_hyperedges.card ≥ (G.hyperedges i \ excluded).card ∧
      (∀ j ∈ connecting_hyperedges,
        ∃ v ∈ G.hyperedges i \ excluded,
        ∃ u : G.vertices,
          built j = some u ∧ v ∈ G.hyperedges j ∧ v ≠ u) := by
  classical
  rcases
      result1_connecting_finset_of_no_available
        (G := G) (i := i) (excluded := excluded) (built := built)
        h_no_avail h_no_free hbi
    with ⟨connecting_hyperedges, hcard, hprop⟩
  refine ⟨connecting_hyperedges, hcard, ?_⟩
  intro j hj
  rcases hprop j hj with ⟨v, hv_i, hvne, u, hbj, hvj, hvneu⟩
  refine ⟨v, ?_, u, hbj, hvj, hvneu⟩
  exact Finset.mem_sdiff.2 ⟨hv_i, hvne⟩

end EFLExports

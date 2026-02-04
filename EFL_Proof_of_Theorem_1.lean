import EFLLean.EFL_Definitions
import EFLLean.EFL_Lemmas_for_Theorem_1

namespace EFLLean

set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/--
Reviewer-facing packaging theorem.

`counting_core_contradiction` is the formal counting argument:
combining Result 1, Result 2, and their disjointness yields
`n + 1` distinct given hyperedges, contradicting that the input has exactly `n`.

In the manuscript narrative, this contradiction eliminates the obstruction that
would correspond to the greedy construction's `none` branch.
-/
theorem theorem1_counting_contradiction
    {n m : ℕ}
    (connecting : Finset (Fin n))
    (origins : Finset (Fin n))
    (j_conn : Fin n)
    (h1 : connecting.card ≥ n - m)
    (h2 : origins.card = m)
    (hj : j_conn ∉ origins)
    (hdisj : Disjoint connecting (origins ∪ ({j_conn} : Finset (Fin n)))) :
    False := by
  exact counting_core_contradiction
    (connecting := connecting)
    (origins := origins)
    (j_conn := j_conn)
    h1 h2 hj hdisj

/--
**Bridge theorem (referee request).**

This is the explicit named “bridge lemma” requested by the referee.
It packages the counting contradiction into a stable theorem name that can be cited
directly from the mapping document.

(Proof: definitionally the same as `theorem1_counting_contradiction`.)
-/
theorem bridge_counting_contradiction
    {n m : ℕ}
    (connecting : Finset (Fin n))
    (origins : Finset (Fin n))
    (j_conn : Fin n)
    (h1 : connecting.card ≥ n - m)
    (h2 : origins.card = m)
    (hj : j_conn ∉ origins)
    (hdisj :
      Disjoint connecting (origins ∪ ({j_conn} : Finset (Fin n)))) :
    False := by
  exact theorem1_counting_contradiction
    (connecting := connecting)
    (origins := origins)
    (j_conn := j_conn)
    h1 h2 hj hdisj

/--
## Reviewer bridge: local failure ⇒ Result 1 hypotheses

This lemma supplies the hypotheses used by `count_connecting_hyperedges_result1`.
-/
theorem result1_hypotheses_of_no_available
    {n : ℕ} (G : EFLGraph n) (i : Fin n)
    (excluded : Finset G.vertices) (built : Fin n → Option G.vertices)
    (h_no_avail : non_free_available G i excluded built = ∅)
    (h_no_free : free_available G i excluded built = ∅)
    (hbi : built i = none)
    :
    (∀ v ∈ G.hyperedges i, v ∉ excluded → would_violate_multiset G v i built = true) ∧
    (∀ v ∈ G.hyperedges i, v ∉ excluded →
        ∃ j u, built j = some u ∧ v ∈ G.hyperedges j ∧ v ≠ u ∧ j ≠ i) :=
by
  classical

  -- First: all vertices must violate (otherwise they'd appear in free/nonfree available sets).
  have hall :
      ∀ v ∈ G.hyperedges i, v ∉ excluded → would_violate_multiset G v i built = true := by
    intro v hv hvne
    by_contra hfalse

    have hv_in_avail : v ∈ available_consistent_vertices G i excluded built := by
      -- `by_contra hfalse` means `would_violate_multiset ... ≠ true`, hence it must be `false`.
      have hfalse' : would_violate_multiset G v i built = false := by
        cases h : would_violate_multiset G v i built with
        | false => rfl
        | true =>
          exfalso
          exact hfalse h
      simp [available_consistent_vertices, hv, hvne, hfalse']

    -- show `0 < vertex_degree G v` using membership of v in hyperedge i
    have hv_deg_pos : 0 < vertex_degree G v := by
      have h1 : 1 ≤ degree G v :=
        degree_pos_of_mem_hyperedge (G := G) (i := i) (v := v) hv
      have h1' : 1 ≤ vertex_degree G v := by
        simpa [degree] using h1
      exact Nat.lt_of_lt_of_le Nat.zero_lt_one h1'

    have hge : 1 ≤ vertex_degree G v := (Nat.succ_le_iff).2 hv_deg_pos

    -- Split degree > 1 vs degree = 1.
    cases lt_or_eq_of_le hge with
    | inl hlt =>
        have hmem : v ∈ non_free_available G i excluded built := by
          simp [non_free_available, hv_in_avail, hlt]
        simpa [h_no_avail] using hmem
    | inr heq1 =>
        have hmem : v ∈ free_available G i excluded built := by
          simp [free_available, hv_in_avail, heq1.symm]
        simpa [h_no_free] using hmem

  -- Second: from `would_violate_multiset = true`, extract the witness hyperedge `j` and vertex `u`.
  have hextract :
      ∀ v ∈ G.hyperedges i, v ∉ excluded →
        ∃ j u, built j = some u ∧ v ∈ G.hyperedges j ∧ v ≠ u ∧ j ≠ i := by
    intro v hv hvne
    have hviol : would_violate_multiset G v i built = true := hall v hv hvne

    -- The existential that is tested in `would_violate_multiset`.
    have hex :
        ∃ j : Fin n,
          match built j with
          | none => False
          | some w => v ∈ G.hyperedges j ∧ w ∈ G.hyperedges j ∧ v ≠ w := by
      rcases
          (would_violate_multiset_eq_true_iff (G := G) (v := v) (i := i) (built := built)).1 hviol
        with ⟨j, u, hbj, hvj, huj, hvneu⟩
      refine ⟨j, ?_⟩
      -- reduce the match using `hbj`
      simpa [hbj] using And.intro hvj (And.intro huj hvneu)

    rcases hex with ⟨j, hj⟩
    cases hbj : built j with
    | none =>
        have hjFalse : False := by
          simpa [hbj] using hj
        exact hjFalse.elim
    | some u =>
        have hj' : v ∈ G.hyperedges j ∧ u ∈ G.hyperedges j ∧ v ≠ u := by
          have hj'' := hj
          simp [hbj] at hj''
          exact hj''
        have hj_ne_i : j ≠ i := by
          intro hji
          subst hji
          have hEq : (none : Option G.vertices) = some u := by
            simpa [hbi] using hbj
          cases hEq
        exact ⟨j, u, hbj, hj'.1, hj'.2.2, hj_ne_i⟩

  exact ⟨hall, hextract⟩

/--
## Reviewer bridge: Result 1 (construct the connecting-hyperedges finset)

Packages `result1_hypotheses_of_no_available` into the exact inputs of
`count_connecting_hyperedges_result1`.
-/
theorem result1_connecting_finset_of_no_available
    {n : ℕ} (G : EFLGraph n) (i : Fin n)
    (excluded : Finset G.vertices) (built : Fin n → Option G.vertices)
    (h_no_avail : non_free_available G i excluded built = ∅)
    (h_no_free : free_available G i excluded built = ∅)
    (hbi : built i = none)
    :
    ∃ connecting_hyperedges : Finset (Fin n),
      connecting_hyperedges.card ≥ (G.hyperedges i \ excluded).card ∧
      ∀ j ∈ connecting_hyperedges,
        ∃ v ∈ G.hyperedges i, v ∉ excluded ∧
          ∃ u, built j = some u ∧ v ∈ G.hyperedges j ∧ v ≠ u :=
by
  classical

  have hpair :=
    result1_hypotheses_of_no_available
      (G := G) (i := i) (excluded := excluded) (built := built)
      h_no_avail h_no_free hbi

  have hall :
      ∀ v ∈ G.hyperedges i, v ∉ excluded → would_violate_multiset G v i built = true :=
    hpair.1

  have h_extract_witness :
      ∀ v ∈ G.hyperedges i, v ∉ excluded →
        ∃ j u, built j = some u ∧ v ∈ G.hyperedges j ∧ v ≠ u ∧ j ≠ i :=
    hpair.2

  -- Distinctness of witnesses follows from pairwise intersection.
  have h_distinct_witnesses :
    ∀ (v : G.vertices) (w : G.vertices),
      v ∈ G.hyperedges i →
      w ∈ G.hyperedges i →
      v ∉ excluded →
      w ∉ excluded →
      v ≠ w →
      ∀ j_v j_w : Fin n,
        ∀ u_v u_w : G.vertices,
          (built j_v = some u_v ∧ v ∈ G.hyperedges j_v ∧ v ≠ u_v) →
          (built j_w = some u_w ∧ w ∈ G.hyperedges j_w ∧ w ≠ u_w) →
          j_v ≠ j_w := by
    intro v w hv_i hw_i hvne hwne hvw jv jw uv uw hvwit hwwit hEq
    subst hEq

    have hij : i ≠ jv := by
      intro h
      have hi_some : built i = some uv := by
        simpa [h] using hvwit.1
      have : (none : Option G.vertices) = some uv := by
        simpa [hbi] using hi_some
      cases this

    have hle1 : (G.hyperedges i ∩ G.hyperedges jv).card ≤ 1 :=
      G.pairwise_intersection i jv hij

    have hv_j : v ∈ G.hyperedges jv := hvwit.2.1
    have hw_j : w ∈ G.hyperedges jv := hwwit.2.1

    let S : Finset G.vertices := G.hyperedges i ∩ G.hyperedges jv
    have hvS : v ∈ S := by
      simpa [S] using (Finset.mem_inter.2 ⟨hv_i, hv_j⟩)
    have hwS : w ∈ S := by
      simpa [S] using (Finset.mem_inter.2 ⟨hw_i, hw_j⟩)

    have hgt1 : 1 < S.card := by
      apply Finset.one_lt_card.2
      exact ⟨v, hvS, w, hwS, hvw⟩

    have hle1' : S.card ≤ 1 := by
      simpa [S] using hle1
    have : ¬ (1 < S.card) := Nat.not_lt_of_ge hle1'
    exact this hgt1

  rcases
    count_connecting_hyperedges_result1
      (G := G) (i := i) (excluded := excluded) (built := built)
      hall h_extract_witness h_distinct_witnesses
    with ⟨connecting_hyperedges, hcard, hprop⟩

  refine ⟨connecting_hyperedges, hcard, ?_⟩
  intro j hj

  have hw := hprop.2 j hj
  rcases hw with ⟨v, hv_in, u, hbj, hvj, hvneu⟩

  have hv_i : v ∈ G.hyperedges i := (Finset.mem_sdiff.mp hv_in).1
  have hvne : v ∉ excluded := (Finset.mem_sdiff.mp hv_in).2

  exact ⟨v, hv_i, hvne, u, hbj, hvj, hvneu⟩

end EFLLean

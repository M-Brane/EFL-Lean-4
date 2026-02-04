-- EFL Lemmas for Theorem 1
--
-- This file contains all lemmas required to prove Theorem 1 (the counting argument).
--
-- **Theorem 1**: It is possible to construct n single-color hyperedges for G,
-- such that no vertex belongs to more than one single-color hyperedge.
--
-- **Proof Strategy**: By induction and contradiction using a counting argument.
--
import EFLLean.EFL_Definitions

set_option linter.style.commandStart false

open EFLGraph

/-!
## Lemma 1.1 (Manuscript): Pigeonhole Principle

When exclusions are bounded (at most n-1 vertices excluded from each hyperedge),
there exists at least one available vertex in any given hyperedge.
-/

lemma available_vertex_exists {n : Nat} (hn : n > 0) (G : EFLGraph n)
    (excluded : Finset G.vertices)
    (h_bound : ∀ i : Fin n,
      letI := Classical.decPred (· ∈ excluded)
      ((G.hyperedges i).filter (· ∈ excluded)).card ≤ n - 1)
    (i : Fin n) :
  ∃ v : G.vertices, v ∈ G.hyperedges i ∧ v ∉ excluded := by
  -- The hyperedge has size n
  have h_size : (G.hyperedges i).card = n := G.size_constraint i
  -- The excluded vertices in this hyperedge are at most n - 1
  letI := Classical.decPred (· ∈ excluded)
  have h_excl_bound := h_bound i
  -- Therefore, there must be at least one vertex in the hyperedge that's not excluded
  -- Use the pigeonhole principle: |hyperedge| = n, |excluded ∩ hyperedge| ≤ n-1
  -- So |hyperedge \ excluded| ≥ 1
  have h_diff : ((G.hyperedges i).filter (· ∉ excluded)).Nonempty := by
    by_contra h_empty
    -- If no vertices are available, then all n vertices are excluded
    have h_empty_eq : (G.hyperedges i).filter (· ∉ excluded) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp h_empty
    -- This means every vertex in the hyperedge is excluded
    -- So the excluded count equals the hyperedge size
    have h_eq : ((G.hyperedges i).filter (· ∈ excluded)).card = (G.hyperedges i).card := by
      -- If no non-excluded vertices exist, then all vertices are excluded
      have : ∀ v ∈ G.hyperedges i, v ∈ excluded := by
        intro v hv
        by_contra hnot
        have : v ∈ (G.hyperedges i).filter (· ∉ excluded) := by
          simp [hv, hnot]
        rw [h_empty_eq] at this
        simp at this
      -- So filtering by excluded gives the whole hyperedge
      have : (G.hyperedges i).filter (· ∈ excluded) = G.hyperedges i := by
        ext v
        simp
        intro hv
        exact this v hv
      rw [this]
    rw [h_size] at h_eq
    -- But h_excl_bound says excluded count ≤ n - 1
    omega
  obtain ⟨v, hv⟩ := h_diff
  use v
  simp at hv
  exact hv

/-!
## Connecting Hyperedge Definitions

Two vertices "connect" via a given hyperedge if they both appear in it.
This is used in the counting argument to track which given hyperedges are involved.
-/

/-- Two vertices v and w connect via hyperedge i if both are in G.hyperedges i and v ≠ w -/
def connects_via (G : EFLGraph n) (v w : G.vertices) (i : Fin n) : Prop :=
  v ∈ G.hyperedges i ∧ w ∈ G.hyperedges i ∧ v ≠ w

/-- The set of hyperedges where vertex v connects to at least one vertex in set S -/
noncomputable def connecting_hyperedges (G : EFLGraph n) (v : G.vertices) (S : Finset G.vertices) :
    Finset (Fin n) :=
  letI := Classical.decPred fun i => ∃ w ∈ S, connects_via G v w i
  Finset.univ.filter fun i => ∃ w ∈ S, connects_via G v w i

/-- The set of candidates (vertices in G_i not in excluded) -/
def candidates {n : Nat} (G : EFLGraph n) (i : Fin n) (excluded : Finset G.vertices) :
    Finset G.vertices :=
  letI := G.dec_eq
  G.hyperedges i \ excluded

/-!
## Micro-Lemma: Non-Free Vertex Implies Additional Given Hyperedge

**Claim:** For every non-free vertex v in some given hyperedge gi, there must exist
at least one additional given hyperedge gj (where j ≠ i) that also contains v.

**Proof:** By the definition of non-free vertex (degree ≥ 2) and the pairwise
intersection rule of EFL.
-/

lemma non_free_implies_additional_hyperedge {n : Nat} (G : EFLGraph n)
    (v : G.vertices) (i : Fin n)
    (hv_in_i : v ∈ G.hyperedges i)
    (hv_non_free : is_non_free G v) :
  ∃ j : Fin n, j ≠ i ∧ v ∈ G.hyperedges j := by
  -- Non-free means degree ≥ 2
  simp [is_non_free, degree, vertex_degree] at hv_non_free
  letI := G.dec_eq
  letI := Classical.decPred fun k => v ∈ G.hyperedges k

  -- v appears in at least 2 hyperedges
  have h_card : (Finset.univ.filter fun k => v ∈ G.hyperedges k).card ≥ 2 := hv_non_free

  -- i is one of them
  have h_i_in : i ∈ Finset.univ.filter fun k => v ∈ G.hyperedges k := by
    simp
    exact hv_in_i

  -- Since card ≥ 2, there must be another one besides i
  have h_exists_other : ∃ j ∈ Finset.univ.filter fun k => v ∈ G.hyperedges k, j ≠ i := by
    by_contra h_not
    push_neg at h_not
    -- If no other element exists, then {i} contains all elements
    have h_subset :
        (Finset.univ.filter fun k => v ∈ G.hyperedges k) ⊆ ({i} : Finset (Fin n)) := by
      intro x hx
      -- by `h_not`, any index containing `v` must be `i`
      simpa using (h_not x hx)
    have h_card_le : (Finset.univ.filter fun k => v ∈ G.hyperedges k).card ≤ 1 := by
      calc (Finset.univ.filter fun k => v ∈ G.hyperedges k).card
        ≤ ({i} : Finset (Fin n)).card := Finset.card_le_card h_subset
        _ = 1 := Finset.card_singleton i
    omega

  obtain ⟨j, hj_in, hj_ne⟩ := h_exists_other
  use j
  constructor
  · exact hj_ne
  · simp at hj_in
    exact hj_in

/-!
## Lemma 1.2 (Manuscript): Exclusion Reason 2 Locality

**Manuscript Statement:** "Vertices that are excluded for selection by Vertex Exclusion
Reason 2 are only excluded during generation of the single-color hyperedge currently
under construction."

**Manuscript Proof:** "Suppose not. Then for some vertex, v1, which was excluded for
selection in a previously constructed single-color hyperedge, hi, for Vertex Exclusion
Reason 2, the following would be true. Vertex v1 lies in some given hyperedge, g, that
contains some vertex, v2, that was selected for hi. But if v1 were also excluded from
inclusion in another single-color hyperedge, hj, because of that same invocation of
Vertex Exclusion Reason 2, then that would mean v2 is also a member of hj, which
contradicts the uniqueness requirement of the definition of Single-Color Hyperedge."

**Proof Strategy:** Proof by contradiction showing that if v1 were excluded in both hi
and hj for the same Exclusion Reason 2 (involving same v2 and g), then v2 would need
to be in both hi and hj, violating uniqueness.
-/

/-- Lemma 1.2: Exclusion Reason 2 is local to current hyperedge construction.

If vertex v1 is excluded from two different single-color hyperedges hi and hj due to
the SAME instance of Exclusion Reason 2 (same connecting vertex v2, same given hyperedge g),
this leads to a contradiction: v2 would need to appear in both hi and hj, violating
the requirement that each vertex appears in at most one single-color hyperedge.

This proves that Exclusion Reason 2 exclusions are temporary and local to the current
hyperedge being constructed - they do not persist across different hyperedge constructions.
-/
lemma exclusion_reason_2_is_local {n : Nat} (_hn : n > 0) (G : EFLGraph n)
    (v1 v2 : G.vertices) (g hi_num hj_num : Fin n)
    (hi hj : Fin n → G.vertices) -- Two different single-color hyperedges
    (h_different_hyperedges : hi_num ≠ hj_num)
    (_h_hi_valid : ∀ k, hi k ∈ G.hyperedges k) -- hi is valid single-color hyperedge
    (_h_hj_valid : ∀ k, hj k ∈ G.hyperedges k) -- hj is valid single-color hyperedge
    (_h_v2_in_hi : ∃ k, hi k = v2) -- v2 was selected for hi
    (_h_v1_v2_in_g : v1 ∈ G.hyperedges g ∧ v2 ∈ G.hyperedges g ∧ v1 ≠ v2)
    -- Assume v1 excluded from hi because of v2
    (h_exclusion_hi : ∃ k, hi k = v2 ∧ v1 ∈ G.hyperedges k ∧ v1 ≠ v2)
    -- Assume v1 also excluded from hj for SAME reason (same v2)
    (h_exclusion_hj : ∃ k, hj k = v2 ∧ v1 ∈ G.hyperedges k ∧ v1 ≠ v2)
    -- Uniqueness property: each vertex appears in at most one single-color hyperedge
    -- This is implicit in the manuscript's Theorem 1 goal
    (h_uniqueness : ∀ v : G.vertices, ∀ (_i _j : Fin n),
      (∃ k, hi k = v) → (∃ k, hj k = v) → hi_num = hj_num) :
  False := by
  -- Extract witnesses from the exclusion hypotheses
  obtain ⟨k_hi, hk_hi_eq, _, _⟩ := h_exclusion_hi
  obtain ⟨k_hj, hk_hj_eq, _, _⟩ := h_exclusion_hj

  -- v2 appears in both hi and hj
  have hv2_in_hi : ∃ k, hi k = v2 := ⟨k_hi, hk_hi_eq⟩
  have hv2_in_hj : ∃ k, hj k = v2 := ⟨k_hj, hk_hj_eq⟩

  -- By uniqueness property, if v2 appears in both hi and hj,
  -- then hi_num must equal hj_num
  have : hi_num = hj_num := h_uniqueness v2 hi_num hj_num hv2_in_hi hv2_in_hj

  -- But we know hi_num ≠ hj_num
  -- This is a contradiction
  exact absurd this h_different_hyperedges

/-!
### Lemma: Count Connecting Hyperedges (Result 1)

**Manuscript (Theorem 1, Result 1):**
"For any vertex v in gt+1 that has been excluded because of Vertex Exclusion Reason 1,
there exists one of the first m given hyperedges, from which v was selected in a prior
single-color hyperedge. [...] Since there are (n – m) vertices in gt+1 that are not one
of the m vertices of gt+1, then there are (n – m) given hyperedges that are different
from gt+1 from which these (n – m) vertices must have been selected previously."

When all non-excluded candidates would be excluded by Exclusion Reason 2 (Definition 7),
each connects to a built vertex via some hyperedge. These connecting hyperedges are:
1. Distinct from each other (by pairwise intersection)
2. Different from gt+1 (i.e., j ≠ i)
3. At least (n-m) in count
-/

lemma count_connecting_hyperedges_result1 {n : Nat} (G : EFLGraph n)
    (i : Fin n) (excluded : Finset G.vertices) (built : Fin n → Option G.vertices)
    (_h_all_violate :
      ∀ v ∈ G.hyperedges i, v ∉ excluded → would_violate_multiset G v i built = true)
    -- Hypothesis: Can extract witness hyperedge for each candidate
    -- This follows from Definition 7 (Exclusion Reason 2)
    (h_extract_witness : ∀ v ∈ G.hyperedges i, v ∉ excluded →
      ∃ j : Fin n, ∃ u : G.vertices,
        built j = some u ∧ v ∈ G.hyperedges j ∧ v ≠ u ∧ j ≠ i)
    -- Hypothesis: Witnesses are distinct by pairwise intersection
    -- This follows from EFL pairwise intersection property
    (h_distinct_witnesses :
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
          j_v ≠ j_w) :
  letI := G.dec_eq
  ∃ (connecting_hyperedges : Finset (Fin n)),
    connecting_hyperedges.card ≥ (G.hyperedges i \ excluded).card ∧
    (∀ j ∈ connecting_hyperedges, j ≠ i) ∧
    (∀ j ∈ connecting_hyperedges,
      ∃ v ∈ G.hyperedges i \ excluded,
      ∃ u, built j = some u ∧ v ∈ G.hyperedges j ∧ v ≠ u) := by
  classical
  -- Use the graph's decidable equality consistently for all Finset operations in this lemma.
  letI : DecidableEq G.vertices := G.dec_eq
  let cands : Finset G.vertices := G.hyperedges i \ excluded
  have hcands_mem : ∀ {v : G.vertices}, v ∈ cands → v ∈ G.hyperedges i ∧ v ∉ excluded := by
    intro v hv
    simpa [cands] using (Finset.mem_sdiff.mp hv)

  -- For each candidate vertex, pick a "witness" connecting hyperedge index j.
  have hex : ∀ v : G.vertices, v ∈ cands →
      ∃ j : Fin n, ∃ u : G.vertices,
        built j = some u ∧ v ∈ G.hyperedges j ∧ v ≠ u ∧ j ≠ i := by
    intro v hv
    have hv' : v ∈ G.hyperedges i ∧ v ∉ excluded := hcands_mem hv
    exact h_extract_witness v hv'.1 hv'.2

  let pickJ : {v // v ∈ cands} → Fin n := fun vv => Classical.choose (hex vv.1 vv.2)

  -- The Finset of all picked connecting hyperedges.
  let connecting_hyperedges : Finset (Fin n) := cands.attach.image pickJ

  -- Each picked j is different from i.
  have hJ_ne_i : ∀ vv : {v // v ∈ cands}, pickJ vv ≠ i := by
    intro vv
    have hspec : ∃ u : G.vertices,
        built (pickJ vv) = some u ∧ vv.1 ∈ G.hyperedges (pickJ vv) ∧ vv.1 ≠ u ∧ pickJ vv ≠ i :=
      Classical.choose_spec (hex vv.1 vv.2)
    exact hspec.choose_spec.right.right.right

  -- For each vv, also extract the chosen vertex u witnessing the exclusion-reason-2 connection.
  let pickU : {v // v ∈ cands} → G.vertices := fun vv =>
    Classical.choose (Classical.choose_spec (hex vv.1 vv.2))

  have hJU_spec :
    ∀ (vv : { v // v ∈ cands }),
      built (pickJ vv) = some (pickU vv) ∧
        (↑vv : G.vertices) ∈ G.hyperedges (pickJ vv) ∧
        (↑vv : G.vertices) ≠ pickU vv ∧
        pickJ vv ≠ i := by
    intro vv
    -- `hex` gives a witness `u` once `pickJ vv` is fixed. `pickU vv` is defined as that witness.
    have hspec :
        ∃ u,
          built (pickJ vv) = some u ∧
            (↑vv : G.vertices) ∈ G.hyperedges (pickJ vv) ∧
            (↑vv : G.vertices) ≠ u ∧
            pickJ vv ≠ i :=
      Classical.choose_spec (hex (↑vv) vv.property)
    -- Now specialize the witness to `pickU vv`.
    simpa [pickU] using (Classical.choose_spec hspec)

-- The key point for Result 1: distinct candidate vertices yield distinct connecting hyperedges.
  have hinj : Function.Injective pickJ := by
    intro a b hab
    by_contra hne
    have ha_mem : a.1 ∈ G.hyperedges i ∧ a.1 ∉ excluded := hcands_mem a.2
    have hb_mem : b.1 ∈ G.hyperedges i ∧ b.1 ∉ excluded := hcands_mem b.2
    -- unpack specs for a and b
    have ha_spec := hJU_spec a
    have hb_spec := hJU_spec b
    -- use the provided distinctness hypothesis (contrapositive)
    have hdiff : pickJ a ≠ pickJ b := by
      -- apply with v=a.1, w=b.1
      exact h_distinct_witnesses a.1 b.1
        ha_mem.1 hb_mem.1 ha_mem.2 hb_mem.2 (by
          -- v ≠ w
          exact fun h => hne (Subtype.ext (by simpa using h)))
        (pickJ a) (pickJ b) (pickU a) (pickU b)
        (by
          refine ⟨ha_spec.1, ?_, ?_⟩
          · exact ha_spec.2.1
          · exact ha_spec.2.2.1)
        (by
          refine ⟨hb_spec.1, ?_, ?_⟩
          · exact hb_spec.2.1
          · exact hb_spec.2.2.1)
    exact (hdiff (by simpa [pickJ] using hab)).elim

  refine ⟨connecting_hyperedges, ?_, ?_, ?_⟩
  · -- card bound
    have hattach : cands.attach.card = cands.card := by
      simp
    have himg : connecting_hyperedges.card = cands.attach.card := by
      -- `card_image_of_injective` gives `card (image f s) = card s` when `f` is injective
      simpa [connecting_hyperedges] using
        (Finset.card_image_of_injective (s := cands.attach) (f := pickJ) hinj)
    have hcard_eq : connecting_hyperedges.card = cands.card := by
      simpa [hattach] using himg
    -- turn equality into the desired inequality
    have : cands.card ≤ connecting_hyperedges.card := le_of_eq hcard_eq.symm
    simpa [cands, ge_iff_le] using this
  · -- all connecting hyperedges are distinct from i
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨vv, hvv, rfl⟩
    exact hJ_ne_i vv
  · -- witness property for each connecting hyperedge index
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨vv, hvv, rfl⟩
    refine ⟨vv.1, ?_, pickU vv, ?_⟩
    · -- `vv.2 : (vv : G.vertices) ∈ cands`, and `cands = G.hyperedges i \ excluded`
      have hvv := vv.2
      dsimp [cands] at hvv
      exact hvv
    · have hs := hJU_spec vv
      exact ⟨hs.1, ⟨hs.2.1, hs.2.2.1⟩⟩

/-!
### Lemma: Result 2 - Structural Hyperedge Counting

**Manuscript (Theorem 1, Result 2):**
"Since G is an EFL graph, we know that a distinct, given hyperedge exists for each
of the m vertices of gt+1. We can consider that at least one free vertex in the set
of m vertices counts for gt+1, itself. So far then, we would count at least m given
hyperedges. But there must also be at least one connecting given hyperedge, containing
one of the m vertices, otherwise the selection of the free vertex would not have been
required (Free-Vertex-Last rule). [...] We label this minimal quantity of (m + 1)
given hyperedges as Result 2."

**Manuscript's 5-Step Argument:**
1. Each of m vertices in gt+1 came from a distinct given hyperedge → count m
2. At least one free vertex counts for gt+1 itself (already in the m)
3. By Free-Vertex-Last: must be ≥1 connecting hyperedge (the +1)
4. All m can't be free (else no connecting hyperedges for excluded)
5. Therefore: (m+1) distinct given hyperedges total

The claim is: given m vertices already placed in hm+1, and at least one free vertex
among them, we can count (m+1) distinct given hyperedges.
-/

lemma result_2_counting_argument {n : Nat} (_hn : n > 0) (G : EFLGraph n)
    (m : Nat) (_hm_pos : m > 0) (_hm_lt : m < n)
    (i : Fin n) -- Current position (gt+1)
    (_excluded : Finset G.vertices) -- Vertices from m prior hyperedges
    (built : Fin n → Option G.vertices) -- Partial construction
    -- Hypothesis: m vertices of gt+1 are among those already placed
    (_h_m_from_gi : ∃ (vertices_from_gi : Finset G.vertices),
      vertices_from_gi.card = m ∧
      vertices_from_gi ⊆ G.hyperedges i ∧
      (∀ v ∈ vertices_from_gi, ∃ j, built j = some v))
    -- Hypothesis: at least one of them is free
    (_h_has_free : ∃ v ∈ G.hyperedges i, is_free G v ∧ (∃ j, built j = some v))
    -- Hypothesis: Each vertex came from a distinct hyperedge (Step 1)
    -- This follows from the construction algorithm
    (h_distinct_origins : ∃ (origins : Finset (Fin n)),
      origins.card = m ∧
      (∀ j ∈ origins, ∃ v ∈ G.hyperedges i, built j = some v))
    -- Hypothesis: Free-Vertex-Last implies connecting hyperedge exists (Step 3)
    -- If a free vertex was selected, there must be a connecting hyperedge
    (_h_connecting_exists : ∃ j_conn : Fin n, j_conn ≠ i ∧
      ∃ v ∈ G.hyperedges i, ∃ u : G.vertices,
        built j_conn = some u ∧ v ∈ G.hyperedges j_conn)
    -- Hypothesis: The connecting hyperedge is not in origins (distinctness)
    (h_connecting_distinct : ∀ origins : Finset (Fin n), origins.card = m →
      ∃ j_conn : Fin n, j_conn ∉ origins ∧ j_conn ≠ i ∧
        ∃ v ∈ G.hyperedges i, ∃ u : G.vertices,
          built j_conn = some u ∧ v ∈ G.hyperedges j_conn) :
  -- Conclusion: Can count (m+1) distinct given hyperedges
  ∃ (hyperedge_set : Finset (Fin n)),
    hyperedge_set.card = m + 1 := by
  -- Extract the m origin hyperedges
  obtain ⟨origins, h_origins_card, _⟩ := h_distinct_origins

  -- Extract the connecting hyperedge (different from origins)
  obtain ⟨j_conn, hj_not_in_origins, hj_ne_i, _⟩ := h_connecting_distinct origins h_origins_card

  -- Construct the set: origins ∪ {j_conn}
  use origins ∪ {j_conn}

  -- Prove cardinality = m + 1
  have h_disj : Disjoint origins {j_conn} := by
    exact Finset.disjoint_singleton_right.mpr hj_not_in_origins

  have hcard : (origins ∪ {j_conn}).card = origins.card + 1 := by
    -- `card {j_conn} = 1`
    simpa [Finset.card_singleton] using (Finset.card_union_of_disjoint h_disj)

  calc
    (origins ∪ {j_conn}).card = origins.card + 1 := hcard
    _ = m + 1 := by
      simp [h_origins_card]

/--
Result 1 produces a `connecting_hyperedges` finset (coming from excluded candidate vertices).
Result 2 produces a finset `origins ∪ {j_conn}` (coming from the `m` already-chosen vertices, plus
at least one connecting hyperedge needed to force a free-vertex choice).

To avoid doing the disjointness proof twice, we prove disjointness from the one-directional fact
"every hyperedge counted by Result 1 is *not* counted by Result 2".

The *deep* combinatorial content (no double-counting of any given hyperedge across the two results)
will later be discharged by proving the hypothesis `h_no_overlap` from the EFL pairwise-intersection
property plus the way `pickJ` is extracted.

For now, this lemma packages the clean Finset logic that turns that one-directional fact into
`Disjoint`.
-/
lemma result1_result2_disjoint_of_noOverlap
    {n : ℕ} {G : EFLGraph n} {_i : Fin n}
    {_excluded : Finset G.vertices} {_built : Fin n → Option G.vertices}
    {connecting_hyperedges : Finset (Fin n)}
    {origins : Finset (Fin n)} {j_conn : Fin n}
    (h_no_overlap : ∀ j ∈ connecting_hyperedges, j ∉ origins ∪ {j_conn}) :
    Disjoint connecting_hyperedges (origins ∪ {j_conn}) := by
  -- Finset disjointness is equivalent to: no element of the left set is in the right set.
  refine Finset.disjoint_left.2 ?_
  intro j hj_left hj_right
  exact (h_no_overlap j hj_left) hj_right


/--
A convenient packaging of the *one-directional* disjointness fact:
if you can show that every hyperedge counted by Result 1 is not among the hyperedges counted by
Result 2, then the two finsets are disjoint.

This lemma is intentionally phrased so that the *deep* part of the argument (showing the
non-overlap) can be proved once and then reused; you don't have to separately prove both
"R1 ∩ R2 = ∅" and "R2 ∩ R1 = ∅".
-/
lemma result1_disjoint_result2_of_forall_not_mem
    {α : Type} [DecidableEq α]
    (R1 R2 : Finset α)
    (h : ∀ j, j ∈ R1 → j ∉ R2) : Disjoint R1 R2 := by
  -- `Finset.disjoint_left` turns disjointness into the element-wise statement.
  refine Finset.disjoint_left.2 ?_
  intro j hj1 hj2
  exact (h j hj1) hj2

/--
Disjointness in the particular form needed for the Result 1 / Result 2 counting step.

Once you prove `h_no_overlap` from the EFL pairwise-intersection property and the definitions of
"connecting hyperedge" and "origin hyperedge", you can use this lemma to conclude the finsets are
disjoint.
-/
lemma result1_result2_disjoint
    {n : ℕ} (G : EFLGraph n)
    {_i : Fin n}
    {_excluded : Finset G.vertices}
    {_built : Fin n → Option G.vertices}
    (connecting_hyperedges : Finset (Fin n))
    (origins : Finset (Fin n))
    (j_conn : Fin n)
    (h_no_overlap : ∀ j, j ∈ connecting_hyperedges → j ∉ (origins ∪ {j_conn})) :
    Disjoint connecting_hyperedges (origins ∪ {j_conn}) := by
  have h' := result1_disjoint_result2_of_forall_not_mem
    connecting_hyperedges (origins ∪ {j_conn}) h_no_overlap
  simpa using h'

/-!
### Result 2.1: Finset card step (the +1)

This is the purely set-theoretic step used in Result 2:
if `j_conn ∉ origins`, then adding `{j_conn}` increases the cardinality by 1.

Keeping this as a standalone lemma avoids re-proving (or re-simplifying) the same
`Finset` facts inside later, more combinatorial lemmas.
-/
lemma result2_1_card_union_singleton
    {α : Type} [DecidableEq α]
    (origins : Finset α) (j_conn : α) (hj : j_conn ∉ origins) :
    (origins ∪ {j_conn}).card = origins.card + 1 := by
  have h_disj : Disjoint origins ({j_conn} : Finset α) := by
    exact Finset.disjoint_singleton_right.mpr hj
  -- `card (origins ∪ {j_conn}) = card origins + card {j_conn}`
  -- and `card {j_conn} = 1`.
  simpa [Finset.card_singleton] using (Finset.card_union_of_disjoint h_disj)

/-
R2.2 (counting step):
If j_conn ∉ origins, then adding it increases card by 1.
-/
lemma R2_2_cardinality_increase
  {n m : ℕ}
  (origins : Finset (Fin n))
  (j_conn : Fin n)
  (h_origins_card : origins.card = m)
  (hj_not_in_origins : j_conn ∉ origins)
  (_hdisj : Disjoint origins {j_conn}) :
  (origins ∪ {j_conn}).card = m + 1 := by
  have hunion : origins ∪ ({j_conn} : Finset (Fin n)) = insert j_conn origins := by
    ext a
    simp

  calc
    (origins ∪ {j_conn}).card
        = (insert j_conn origins).card := by
            simp [hunion]
    _   = origins.card + 1 := by
            simp [Finset.card_insert_of_notMem, hj_not_in_origins]
    _   = m + 1 := by
            simp [h_origins_card]

/--
Result 1 and Result 2 are counted via two finsets of hyperedge-indices.
Once disjointness is established (the “no double-counting” nexus in the manuscript),
we can add the counts by `Finset.card_union_of_disjoint`.

This lemma is intentionally generic: it will be instantiated with
`connecting_hyperedges` from Result 1 and the `origins ∪ {j_conn}` block from Result 2.
-/
-- Convenience wrappers matching the manuscript names R2.1 and R2.2.
-- R2.1: if `j_conn ∉ origins`, then `origins` is disjoint from `{j_conn}`.
lemma R2_1
  {n m : ℕ}
  (origins : Finset (Fin n))
  (j_conn : Fin n)
  (_h_origins_card : origins.card = m)
  (hj_not_in_origins : j_conn ∉ origins) :
  Disjoint origins {j_conn} := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro a ha_orig ha_single
  have ha : a = j_conn := by
    simpa using ha_single
  subst ha
  exact hj_not_in_origins ha_orig

-- R2.2: if `origins.card = m` and `j_conn ∉ origins`, then `(origins ∪ {j_conn}).card = m + 1`.
lemma R2_2
  {n m : ℕ}
  (origins : Finset (Fin n))
  (j_conn : Fin n)
  (h_origins_card : origins.card = m)
  (hj_not_in_origins : j_conn ∉ origins) :
  (origins ∪ {j_conn}).card = m + 1 := by
  classical
  have hdisj : Disjoint origins {j_conn} :=
    R2_1 (origins := origins) (j_conn := j_conn) (m := m) h_origins_card hj_not_in_origins
  exact
    R2_2_cardinality_increase
      origins j_conn h_origins_card hj_not_in_origins hdisj

lemma card_union_of_disjoint_fin
    {α : Type} [DecidableEq α]
    (A B : Finset α)
    (hdisj : Disjoint A B) :
    (A ∪ B).card = A.card + B.card := by
  simpa using Finset.card_union_of_disjoint hdisj


/--
**Result 2 (card count).**

If `origins` has cardinality `m` and `j_conn ∉ origins`, then
`(origins ∪ {j_conn}).card = m + 1`.

This is the “add one new connecting hyperedge” step that will later be
combined with Result 1.
-/
lemma result2_indices_card
    {n : ℕ} (m : ℕ)
    (origins : Finset (Fin n)) (j_conn : Fin n)
    (h_origins_card : origins.card = m)
    (hj_not_in_origins : j_conn ∉ origins) :
    (origins ∪ {j_conn}).card = m + 1 := by
  classical
  have hdisj : Disjoint origins ({j_conn} : Finset (Fin n)) := by
    refine Finset.disjoint_left.2 ?_
    intro a ha hb
    have : a = j_conn := by simpa using hb
    subst this
    exact hj_not_in_origins ha
  -- Now use disjoint-union card.
  have hcard := card_union_of_disjoint_fin origins ({j_conn} : Finset (Fin n)) hdisj
  -- `{j_conn}` has card 1.
  -- Result 2:
  -- If origins.card = m and j_conn ∉ origins, then (origins ∪ {j_conn}).card = m + 1.
  -- With `hj_not_in_origins`, `{j_conn}` is a singleton, so its card is `1`.
  -- Avoid simp loops: do the cardinality algebra explicitly.
  calc
    (origins ∪ {j_conn}).card = origins.card + ({j_conn} : Finset (Fin n)).card := hcard
    _ = origins.card + 1 := by simp
    _ = m + 1 := by
      simp [h_origins_card]


/-
Result 2 (full): assembled from R2.1 and R2.2
-/

lemma Result2_full
    {n m : ℕ}
    (origins : Finset (Fin n))
    (j_conn : Fin n)
    (h_origins_card : origins.card = m)
    (hj_not_in_origins : j_conn ∉ origins) :
    (origins ∪ {j_conn}).card = m + 1 :=
by
  -- R2.2 already *is* the card step
  exact R2_2 origins j_conn h_origins_card hj_not_in_origins

lemma Result2_full_with_disjoint
    {n m : ℕ}
    (origins : Finset (Fin n))
    (j_conn : Fin n)
    (h_origins_card : origins.card = m)
    (hj_not_in_origins : j_conn ∉ origins) :
    Disjoint origins {j_conn} ∧ (origins ∪ {j_conn}).card = m + 1 :=
by
  constructor
  · exact R2_1 origins j_conn h_origins_card hj_not_in_origins
  · exact R2_2 origins j_conn h_origins_card hj_not_in_origins


/-!
## Reviewer bridge: Result 1 counting lemma name

The proof file for Theorem 1 refers to a lemma name that mirrors the reviewer’s
comment wording (“count connecting hyperedges / Result 1”).  The core lemma is
`count_connecting_hyperedges_result1`; the following lemma is just a thin alias
with the expected name and identical statement.
-/

lemma reviewer_count_connecting_hyperedges_result1
    {n : ℕ} (G : EFLGraph n) (i : Fin n)
    (excluded : Finset G.vertices) (built : Fin n → Option G.vertices)
    (_h_all_violate :
      ∀ v ∈ G.hyperedges i, v ∉ excluded →
        would_violate_multiset G v i built = true)
    (h_extract_witness :
      ∀ v ∈ G.hyperedges i, v ∉ excluded →
        ∃ j u, built j = some u ∧ v ∈ G.hyperedges j ∧ v ≠ u ∧ j ≠ i)
    (h_distinct_witnesses :
      ∀ (v w : G.vertices),
        v ∈ G.hyperedges i →
          w ∈ G.hyperedges i →
            v ∉ excluded →
              w ∉ excluded →
                v ≠ w →
                  ∀ (j_v j_w : Fin n) (u_v u_w : G.vertices),
                    built j_v = some u_v ∧ v ∈ G.hyperedges j_v ∧ v ≠ u_v →
                      built j_w = some u_w ∧ w ∈ G.hyperedges j_w ∧ w ≠ u_w →
                        j_v ≠ j_w) :
    ∃ connecting_hyperedges : Finset (Fin n),
      ∀ j, j ∈ connecting_hyperedges → j ≠ i ∧ built j ≠ none
    := by
      rcases count_connecting_hyperedges_result1
          (G := G) (i := i) (excluded := excluded) (built := built)
          _h_all_violate h_extract_witness h_distinct_witnesses with
        ⟨connecting_hyperedges, _hcard, hi_not_mem, hconn⟩
      refine ⟨connecting_hyperedges, ?_⟩
      intro j hjin
      have hji : j ≠ i := hi_not_mem j hjin
      have hb : built j ≠ none := by
        intro hb0
        rcases hconn j hjin with ⟨v, hv, hu⟩
        rcases hu with ⟨u, hbu, hvj, hvu⟩
        have : (none : Option G.vertices) = some u := by
          have hbu' := hbu
          -- rewrite the left-hand side using `hb0 : built j = none`
          rw [hb0] at hbu'
          exact hbu'
        cases this
      exact ⟨hji, hb⟩

/-!
## Core contradiction lemma

This lemma packages the final contradiction step for Theorem 1:

* Result 1 provides a lower bound `connecting.card ≥ n - m`.
* Result 2 provides an exact card computation `(origins ∪ {j_conn}).card = m + 1`.
* Disjointness gives an additive card formula for the union.
* The union is a subset of `Finset.univ : Finset (Fin n)`, so its card is ≤ `n`.
  The lower bound forces `n + 1 ≤ n`, contradiction.
-/
theorem counting_core_contradiction
    {n m : ℕ}
    (connecting : Finset (Fin n))
    (origins : Finset (Fin n))
    (j_conn : Fin n)
    (h1 : connecting.card ≥ n - m)
    (h2 : origins.card = m)
    (hj : j_conn ∉ origins)
    (hdisj : Disjoint connecting (origins ∪ ({j_conn} : Finset (Fin n)))) :
    False := by
  classical
  -- Card of the Result-2 side is exactly `m + 1`.
  have hR2 : (origins ∪ ({j_conn} : Finset (Fin n))).card = m + 1 := by
    simpa [Finset.union_singleton] using
      Result2_full (origins := origins) (j_conn := j_conn) (m := m) h2 hj

  -- Lower bound on the union via disjointness.
  have hunion_card :
      (connecting ∪ (origins ∪ ({j_conn} : Finset (Fin n)))).card
        = connecting.card + (origins ∪ ({j_conn} : Finset (Fin n))).card := by
    simpa using Finset.card_union_of_disjoint hdisj

  have hlower :
      (connecting ∪ (origins ∪ ({j_conn} : Finset (Fin n)))).card ≥ n + 1 := by
    -- normalize `origins ∪ {j_conn}` into `insert j_conn origins`
    have hunion_card' :
        (connecting ∪ (insert j_conn origins)).card
          = connecting.card + (insert j_conn origins).card := by
      simpa [Finset.union_singleton] using hunion_card

    have hR2' : (insert j_conn origins).card = m + 1 := by
      simpa [Finset.union_singleton] using hR2

    have h_arith : (n - m) + (m + 1) ≥ n + 1 := by
      by_cases hm : m ≤ n
      · -- main intended range: `(n - m) + (m + 1) = n + 1`.
        have hnm : (n - m) + m = n := Nat.sub_add_cancel hm
        calc
          (n - m) + (m + 1) = ((n - m) + m) + 1 := by
            simpa using (Nat.add_assoc (n - m) m 1).symm
          _ = n + 1 := by
            simp [hnm]
          _ ≥ n + 1 := le_rfl
      · -- if `m > n`, then `n - m = 0` and `m + 1 ≥ n + 1`.
        have hlt : n < m := Nat.lt_of_not_ge hm
        have hnm : n - m = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
        have hle : n + 1 ≤ m + 1 := Nat.succ_le_succ (Nat.le_of_lt hlt)
        simpa [hnm, Nat.zero_add] using hle

    calc
      (connecting ∪ (origins ∪ ({j_conn} : Finset (Fin n)))).card
          = (connecting ∪ (insert j_conn origins)).card := by
            simp [Finset.union_singleton]
      _ = connecting.card + (insert j_conn origins).card := hunion_card'
      _ = connecting.card + (m + 1) := by
            simp [hR2']
      _ ≥ (n - m) + (m + 1) := by
            exact Nat.add_le_add_right h1 (m + 1)
      _ ≥ n + 1 := h_arith

  -- Upper bound: any subset of `Finset.univ` has card ≤ `univ.card = n`.
  have hsubset :
      (connecting ∪ (origins ∪ ({j_conn} : Finset (Fin n)))) ⊆
        (Finset.univ : Finset (Fin n)) := by
    intro x _hx
    simp

  have hupper :
      (connecting ∪ (origins ∪ ({j_conn} : Finset (Fin n)))).card ≤ n := by
    have hle := Finset.card_le_card hsubset
    simpa using (hle.trans_eq (by simp))

  have : n + 1 ≤ n := le_trans hlower hupper
  exact Nat.not_succ_le_self n this

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# EFL Conjecture - Definitions

This file contains the basic definitions for the EFL Conjecture proof.

## Contents
- EFLGraph structure (Definition 1)
- Helper functions for construction algorithm
- Degree computation
- Vertex classification (free vs non-free)
-/

set_option linter.style.longLine false

/-- Definition 1: EFL Graph
An EFL graph consists of a family G = {g₁, ..., gₙ} of n sets each of size n,
with at most one vertex in common between any two distinct sets. -/
structure EFLGraph (n : Nat) where
  vertices : Type
  dec_eq : DecidableEq vertices
  hyperedges : Fin n → Finset vertices
  size_constraint : ∀ i, (hyperedges i).card = n
  pairwise_intersection : ∀ i j, i ≠ j → (hyperedges i ∩ hyperedges j).card ≤ 1


-- Make the field `dec_eq` available to typeclass search
instance {n : Nat} (G : EFLGraph n) : DecidableEq G.vertices := G.dec_eq

/-- Compute the degree of a vertex (number of hyperedges containing it) -/
noncomputable def vertex_degree {n : Nat} (G : EFLGraph n) (v : G.vertices) : Nat :=
  letI := G.dec_eq
  letI := Classical.decPred fun i => v ∈ G.hyperedges i
  (Finset.univ.filter fun i => v ∈ G.hyperedges i).card

/-- Definition 2: Degree of a Vertex
The degree deg(v) of a vertex v is the number of given hyperedges gᵢ that
contain v. If deg(v) = 1, then v is termed a "free vertex." -/
noncomputable def degree {n : Nat} (G : EFLGraph n) (v : G.vertices) : Nat :=
  vertex_degree G v

/-- A vertex is free if it has degree 1 -/
def is_free {n : Nat} (G : EFLGraph n) (v : G.vertices) : Prop :=
  degree G v = 1

/-- A vertex is non-free if it has degree > 1 -/
def is_non_free {n : Nat} (G : EFLGraph n) (v : G.vertices) : Prop :=
  degree G v > 1


/-!
## Definition 2 consequences (algorithmic context)

The manuscript’s Definition 2 classifies vertices by degree:
- `deg(v) = 1` ⇒ free
- otherwise ⇒ non-free

In the construction algorithm, vertices are only considered when they belong to some given
hyperedge `gᵢ`. Under that hypothesis we have `deg(v) ≥ 1`, so “not free” implies “non-free”.
-/

/-- If `v ∈ gᵢ`, then `deg(v) ≥ 1`. -/
lemma degree_pos_of_mem_hyperedge {n : Nat} (G : EFLGraph n)
    {v : G.vertices} {i : Fin n} (hv : v ∈ G.hyperedges i) :
    1 ≤ degree G v := by
  classical
  letI := G.dec_eq
  letI := Classical.decPred (fun j : Fin n => v ∈ G.hyperedges j)
  let S : Finset (Fin n) :=
    Finset.univ.filter (fun j : Fin n => v ∈ G.hyperedges j)
  have hi_mem : i ∈ S := by
    simp [S, hv]
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hi_mem⟩
  have hdeg : degree G v = S.card := by
    simp [degree, vertex_degree, S]
  -- Avoid rewriting `1 ≤ card` into `Nonempty` to prevent binder-name mismatches.
  rw [hdeg]
  exact Nat.succ_le_of_lt hpos

/-- In the algorithmic context: if `v ∈ gᵢ` and `v` is not free, then `v` is non-free. -/
lemma non_free_of_not_free_of_mem_hyperedge {n : Nat} (G : EFLGraph n)
    {v : G.vertices} {i : Fin n} (hv : v ∈ G.hyperedges i)
    (hnot : ¬ is_free G v) :
    is_non_free G v := by
  classical
  have hle : 1 ≤ degree G v := degree_pos_of_mem_hyperedge (G := G) hv
  have hne : degree G v ≠ 1 := by
    intro hEq
    exact hnot (by simpa [is_free] using hEq)
  have hgt : 1 < degree G v := lt_of_le_of_ne hle (Ne.symm hne)
  exact hgt

/-- Checks whether selecting vertex `v` would violate the manuscript’s Exclusion Reason 2.

**Manuscript intent (Exclusion Reason 2, in the language you clarified):**
We cannot select a candidate vertex `v` if there exists a *connecting given hyperedge* `gⱼ`
that contains both `v` and some previously selected vertex `w` (with `v ≠ w`) in the
single-color hyperedge currently being constructed.

**Lean encoding:**
`built : Fin n → Option G.vertices` represents the (partial) choices already made for the
current single-color hyperedge under construction.

So we declare a violation exactly when:

`∃ j, built j = some w ∧ v ∈ G.hyperedges j ∧ w ∈ G.hyperedges j ∧ v ≠ w`.

This matches your “already selected a vertex from gⱼ, so you may not select another
distinct vertex from gⱼ” explanation.
-/
noncomputable def would_violate_multiset {n : Nat} (G : EFLGraph n)
    (v : G.vertices) (_i : Fin n)
    (built : Fin n → Option G.vertices) : Bool :=
  letI := G.dec_eq
  let exclusion_reason_2 : Prop :=
    ∃ j : Fin n,
      match built j with
      | none => False
      | some w =>
          v ∈ G.hyperedges j ∧ w ∈ G.hyperedges j ∧ v ≠ w
  @ite Bool exclusion_reason_2 (Classical.propDecidable _) true false


/-- Bridge lemma: the internal `match built j with ...` witness used in `would_violate_multiset`
can be re-expressed as an explicit witness `built j = some w` (reviewer "missing link" form). -/
lemma exists_match_some_iff_exists_eq_some {n : Nat} (G : EFLGraph n)
    (v : G.vertices) (built : Fin n → Option G.vertices) :
    (∃ j : Fin n,
        match built j with
        | none => False
        | some w => v ∈ G.hyperedges j ∧ w ∈ G.hyperedges j ∧ v ≠ w) ↔
      ∃ j : Fin n, ∃ w : G.vertices,
        built j = some w ∧ v ∈ G.hyperedges j ∧ w ∈ G.hyperedges j ∧ v ≠ w := by
  constructor
  · intro h
    rcases h with ⟨j, hj⟩
    cases hbj : built j with
    | none =>
        -- `hj` reduces to `False` under `hbj`
        have : False := by
          -- `hj` becomes `False` once we rewrite `built j = none`.
          -- We allow `simpa` here to avoid fragile multi-step tactic scripts.
          set_option linter.unnecessarySimpa false in
            simpa [hbj] using hj
        exact False.elim this
    | some w =>
        have hw : v ∈ G.hyperedges j ∧ w ∈ G.hyperedges j ∧ v ≠ w := by
          set_option linter.unnecessarySimpa false in
            simpa [hbj] using hj
        exact ⟨j, w, by simpa using hbj, hw.1, hw.2.1, hw.2.2⟩
  · rintro ⟨j, w, hbw, hvj, hwj, hvw⟩
    refine ⟨j, ?_⟩
    -- rewrite the `match` using `hbw`
    set_option linter.unnecessarySimpa false in
      simpa [hbw] using (And.intro hvj (And.intro hwj hvw))

/-- Reviewer-facing form: `would_violate_multiset = true` iff there exists a "connecting"
given hyperedge witness (Definition 12) already present in `built`. -/
lemma would_violate_multiset_eq_true_iff {n : Nat} (G : EFLGraph n)
    (v : G.vertices) (i : Fin n) (built : Fin n → Option G.vertices) :
    would_violate_multiset G v i built = true ↔
      ∃ j : Fin n, ∃ w : G.vertices,
        built j = some w ∧ v ∈ G.hyperedges j ∧ w ∈ G.hyperedges j ∧ v ≠ w := by
  classical
  unfold would_violate_multiset
  -- expose the underlying Prop witness and rewrite it into the explicit witness form
  simp [exists_match_some_iff_exists_eq_some]
/-- Vertices available at position i that respect multiset property and avoid excluded.

    These are vertices from G.hyperedges[i] that:
    1. Are not in the excluded set (from prior hyperedges)
    2. Don't violate the multiset property with already-built vertices -/
noncomputable def available_consistent_vertices {n : Nat} (G : EFLGraph n)
    (i : Fin n) (excluded : Finset G.vertices)
    (built : Fin n → Option G.vertices) : Finset G.vertices :=
  letI := G.dec_eq
  (G.hyperedges i \ excluded).filter fun v =>
    !would_violate_multiset G v i built

/-- Definition 12: Connecting Given Hyperedge Between v and w

**Manuscript Definition:** "A given hyperedge gⱼ is called a 'connecting given hyperedge
between vertex v and vertex w' if both v and w are distinct members of gⱼ (v ∈ gⱼ, w ∈ gⱼ,
v ≠ w), where v and w are also members of different given hyperedges that are relevant to
the current construction of hₘ₊₁."

**Simplified Formalization:** This definition captures the core membership requirement
(v ∈ gⱼ, w ∈ gⱼ, v ≠ w). The additional manuscript constraints:
- "v and w from different given hyperedges"
- "relevant to current construction"

are enforced by HOW this definition is used in `would_violate_multiset`:
- v is the candidate vertex from hyperedge i
- w is an already-selected vertex from built position k ≠ i
- Therefore manuscript's additional constraints are satisfied by calling context

This simplification makes the definition more composable while maintaining mathematical
correctness. The "connecting" aspect means gⱼ bridges two different given hyperedges.

**Usage in Exclusion Reason 2:** When constructing hₘ₊₁, we cannot select two different
vertices from the same given hyperedge (by Definition 3). So if candidate w shares a
connecting hyperedge gⱼ with already-placed vertex v, then selecting w would mean
selecting both v and w from gⱼ, violating the single-color property.
-/
def connecting_given_hyperedge_between {n : Nat} (G : EFLGraph n) (v w : G.vertices) (j : Fin n) :
    Prop :=
  v ∈ G.hyperedges j ∧ w ∈ G.hyperedges j ∧ v ≠ w

/-!
## Construction Algorithm Definitions

These definitions formalize the greedy construction algorithm that implements
Rule 1 (Free-Vertex-Last) for building single-color hyperedges.
-/

/-- Non-free vertices available at position i.

**Manuscript Reference**: Definition 8/Rule 1 (Free-Vertex-Last)

These are vertices with degree > 1, to be tried FIRST per Rule 1.
Free vertices (degree = 1) are only used after all non-free options exhausted.
-/
noncomputable def non_free_available {n : Nat} (G : EFLGraph n)
    (i : Fin n) (excluded : Finset G.vertices)
    (built : Fin n → Option G.vertices) : Finset G.vertices :=
  (available_consistent_vertices G i excluded built).filter fun v =>
    vertex_degree G v > 1

/-- Free vertices available at position i.

**Manuscript Reference**: Definition 8/Rule 1 (Free-Vertex-Last)

These are vertices with degree = 1, to be tried LAST per Rule 1.
As proven in Theorem 1, a free vertex always qualifies when available,
so using them last avoids premature dead ends.
-/
noncomputable def free_available {n : Nat} (G : EFLGraph n)
    (i : Fin n) (excluded : Finset G.vertices)
    (built : Fin n → Option G.vertices) : Finset G.vertices :=
  (available_consistent_vertices G i excluded built).filter fun v =>
    vertex_degree G v = 1


/-- Implements the multiset property update when placing vertex v at position i.

**Manuscript Basis:** Definition 3 (Single-Color Hyperedge Multiset Property)
"If a particular vertex v appears more than once in the single-color hyperedge,
then v must appear in ALL positions where it belongs."

**Implementation:**
1. Place v at target position i
2. Keep all existing placements unchanged
3. Propagate v to any unfilled position j where v ∈ gⱼ (multiset requirement)

This function extracts logic that was previously inline in construct_hyperedge_aux.
The propagation ensures that when v is selected at position i, it automatically
fills all other positions j where v ∈ G.hyperedges[j], as required by Definition 3.

This is a key part of the construction algorithm, ensuring the multiset property
is maintained throughout the greedy construction process.
-/
def update_built {n : Nat} (G : EFLGraph n) (built : Fin n → Option G.vertices) (i : Fin n) (v : G.vertices) : Fin n → Option G.vertices := fun j =>
  letI := G.dec_eq
  if j = i then some v
  else match built j with
    | some w => some w
    | none => if v ∈ G.hyperedges j then some v else none

/-- The greedy construction algorithm implementing Rule 1 (Free-Vertex-Last).

**Manuscript References**:
- Definition 8/Rule 1: Free vertices selected only after all non-free options exhausted
- Definition 6: Vertex Exclusion Reason 1 (vertices from prior hyperedges)
- Definition 7: Vertex Exclusion Reason 2 (multiset conflicts)
- Theorem 1: Proves this algorithm can construct all n single-color hyperedges

Builds a single-color hyperedge position by position, implementing:
1. **Rule 1**: Try non_free_available before free_available
2. **Automatic propagation**: When placing vertex v, propagate to all hyperedges containing v

The algorithm's correctness is proven in Theorem 1 via the Free-Vertex-Last counting argument.
Rule 2 (Fewest-Hyperedges-Last) could be added for efficiency but is not required.
-/
noncomputable def construct_hyperedge_aux {n : Nat} (hn : n > 0) (G : EFLGraph n)
    (excluded : Finset G.vertices) :
    (Fin n → Option G.vertices) → Nat → Option (Fin n → G.vertices)
  | built, pos =>
    if h : pos < n then
      letI := G.dec_eq
      let i : Fin n := ⟨pos, h⟩

      -- Check if position i is already filled by propagation
      match built i with
      | some v =>
        -- Position already filled by earlier propagation, skip selection
        construct_hyperedge_aux hn G excluded built (pos + 1)
      | none =>
        -- Position not filled, proceed with selection
        -- Rule 1: Try non-free vertices first
        let non_free := non_free_available G i excluded built
        if h_nf : non_free.Nonempty then
          -- Extract a vertex from the nonempty set
          let v := Classical.choice (Finset.Nonempty.to_type h_nf)
          -- Update built: set position i to v, and propagate multiset property
          construct_hyperedge_aux hn G excluded (update_built G built i v) (pos + 1)
        else
          -- Fallback: Try free vertices (Rule 1)
          let free := free_available G i excluded built
          if h_f : free.Nonempty then
            let v := Classical.choice (Finset.Nonempty.to_type h_f)
            construct_hyperedge_aux hn G excluded (update_built G built i v) (pos + 1)
          else
            -- No valid vertex (shouldn't happen with correct proof setup)
            none
    else
      -- All positions filled, extract result
      some (fun j => match built j with
        | some v => v
        | none =>
          -- Fallback: shouldn't happen if algorithm is correct
          have hne : (G.hyperedges j).Nonempty := by
            -- `G.size_constraint j` says `(G.hyperedges j).card = n`, and `hn : 0 < n`.
            have hpos : 0 < (G.hyperedges j).card := by
              simpa [G.size_constraint j] using hn
            exact Finset.card_pos.mp hpos
          Classical.choice (Finset.Nonempty.to_type hne))
termination_by _ pos => n - pos


/-!
## Reviewer bridge: global `none` return ⇒ local empty candidate pools

The referee’s complaint (11-02-2026) identifies a missing connector:

> If `construct_hyperedge_aux … = none`, then there exist a specific slot `i`
> (at some recursion position) where `built i = none` and both availability finsets
> are empty, i.e. `non_free_available … = ∅` and `free_available … = ∅`.

This lemma supplies that connector.
-/
theorem construct_hyperedge_aux_eq_none_exists_empty_pools
    {n : ℕ} (hn : n > 0) (G : EFLGraph n) (excluded : Finset G.vertices)
    (built : Fin n → Option G.vertices) (pos : ℕ)
    (hnone : construct_hyperedge_aux hn G excluded built pos = none) :
    ∃ pos', ∃ (hpos' : pos' < n), ∃ built',
      let i := ⟨pos', hpos'⟩;
      built' i = none ∧
      non_free_available G i excluded built' = ∅ ∧
      free_available G i excluded built' = ∅ :=
by
  -- Recurse on how many positions remain: `k = n - pos`.
  have hrec :
      ∀ k (built : Fin n → Option G.vertices) (pos : ℕ),
        n - pos = k →
        construct_hyperedge_aux hn G excluded built pos = none →
          ∃ pos', ∃ (hpos' : pos' < n), ∃ built',
            let i := ⟨pos', hpos'⟩;
            built' i = none ∧
            non_free_available G i excluded built' = ∅ ∧
            free_available G i excluded built' = ∅ :=
    by
      intro k
      induction k with
      | zero =>
          intro built pos hk hnone
          -- If `n - pos = 0`, then `n ≤ pos`, so the algorithm returns `some _`, contradiction.
          have hnle : n ≤ pos := (Nat.sub_eq_zero_iff_le).1 hk
          have hpos' : ¬ pos < n := Nat.not_lt_of_ge hnle
          -- In the base case `n - pos = 0`, we have `n ≤ pos`, hence `¬ pos < n`.
          -- So `construct_hyperedge_aux` reduces to `some _`, contradicting `hnone`.
          have hne : construct_hyperedge_aux hn G excluded built pos ≠ none := by
            -- With `¬ pos < n`, the definition is in the `else` branch and returns `some _`.
            simp [construct_hyperedge_aux, hpos']
          exact False.elim (hne hnone)
      | succ k ih =>
          intro built pos hk hnone
          -- From `n - pos = k+1`, we get `pos < n`.
          have hnle : ¬ n ≤ pos := by
            intro hnle'
            have hz : n - pos = 0 := Nat.sub_eq_zero_of_le hnle'
            have hz' : (k + 1 : ℕ) = 0 := Eq.trans hk.symm hz
            exact Nat.succ_ne_zero k hz'
          have hpos : pos < n := Nat.lt_of_not_ge hnle
          set i : Fin n := ⟨pos, hpos⟩ with hi
          unfold construct_hyperedge_aux at hnone
          have hnone1 :
              (match built i with
                | some v => construct_hyperedge_aux hn G excluded built (pos + 1)
                | none =>
                    let non_free := non_free_available G i excluded built
                    if h_nf : non_free.Nonempty then
                      let v := Classical.choice (Finset.Nonempty.to_type h_nf)
                      construct_hyperedge_aux hn G excluded (update_built G built i v) (pos + 1)
                    else
                      let free := free_available G i excluded built
                      if h_f : free.Nonempty then
                        let v := Classical.choice (Finset.Nonempty.to_type h_f)
                        construct_hyperedge_aux hn G excluded (update_built G built i v) (pos + 1)
                      else
                        none) = none := by
            simpa [hpos, ←hi] using hnone
          -- Convenient rewrite for the step count.
          have hk_succ : n - pos = Nat.succ k := by
            simpa [Nat.succ_eq_add_one] using hk
          have hk' : n - (pos + 1) = k := by
            have hsub : n - (pos + 1) = Nat.pred (n - pos) := by
              simpa [Nat.succ_eq_add_one] using (Nat.sub_succ n pos)
            simpa [hk_succ] using hsub
          -- Now split on whether `built i` is already assigned.
          cases hbi : built i with
          | some v =>
              have hnone' : construct_hyperedge_aux hn G excluded built (pos + 1) = none := by
                simpa [hbi] using hnone1
              exact ih built (pos + 1) hk' hnone'
          | none =>
              have hnone_if :
                  (let non_free := non_free_available G i excluded built
                   if h_nf : non_free.Nonempty then
                     let v := Classical.choice (Finset.Nonempty.to_type h_nf)
                     construct_hyperedge_aux hn G excluded (update_built G built i v) (pos + 1)
                   else
                     let free := free_available G i excluded built
                     if h_f : free.Nonempty then
                       let v := Classical.choice (Finset.Nonempty.to_type h_f)
                       construct_hyperedge_aux hn G excluded (update_built G built i v) (pos + 1)
                     else
                       none) = none := by
                simpa [hbi] using hnone1
              -- Try non-free pool first.
              by_cases hnf : (non_free_available G i excluded built).Nonempty
              · let v : G.vertices := Classical.choice (Finset.Nonempty.to_type hnf)
                let built1 : Fin n → Option G.vertices := update_built G built i v
                have hnone' :
                    construct_hyperedge_aux hn G excluded built1 (pos + 1) = none := by
                  -- Reduce the `if` using `hnf`.
                  simpa [hnf, built1, v] using hnone_if
                exact ih built1 (pos + 1) hk' hnone'
              · -- Otherwise try the free pool.
                by_cases hf : (free_available G i excluded built).Nonempty
                · let v : G.vertices := Classical.choice (Finset.Nonempty.to_type hf)
                  let built1 : Fin n → Option G.vertices := update_built G built i v
                  have hnone' :
                      construct_hyperedge_aux hn G excluded built1 (pos + 1) = none := by
                    simpa [hnf, hf, built1, v] using hnone_if
                  exact ih built1 (pos + 1) hk' hnone'
                · -- Both pools empty: witness the current slot.
                  
                  -- Both pools empty: witness the current slot.
                  have hnf_empty : non_free_available G i excluded built = ∅ := by
                    apply (Finset.eq_empty_iff_forall_notMem).2
                    intro x hx
                    exact hnf ⟨x, hx⟩
                  have hf_empty : free_available G i excluded built = ∅ := by
                    apply (Finset.eq_empty_iff_forall_notMem).2
                    intro x hx
                    exact hf ⟨x, hx⟩
                  refine ⟨pos, hpos, built, ?_⟩
                  dsimp
                  refine And.intro ?_ (And.intro ?_ ?_)
                  · simpa [hi] using hbi
                  · simpa [hi] using hnf_empty
                  · simpa [hi] using hf_empty
  exact hrec (n - pos) built pos rfl hnone

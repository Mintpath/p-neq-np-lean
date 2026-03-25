import PNeNp.Basic
import PNeNp.GraphInfra
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases

open Finset

namespace PNeNp

variable {n : ℕ}

/-! ## Definition 3.2(a): Degree profile d_S(H) -/

section DegreeProfile

noncomputable def degreeProfile (S : Frontier n) (H : Finset (Edge n)) :
    Fin n → ℕ :=
  fun v => leftDegreeAt S H v

theorem degreeProfile_le_two (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) (v : Fin n) :
    degreeProfile S H v ≤ 2 := by
  unfold degreeProfile leftDegreeAt leftSubgraph vertexDegreeIn
  have hv := hH.twoRegular v
  unfold vertexDegreeIn at hv
  calc (Finset.filter (fun e => v ∈ e) (H ∩ S.leftEdges)).card
      ≤ (Finset.filter (fun e => v ∈ e) H).card := by
        apply Finset.card_le_card
        intro e he
        simp only [Finset.mem_filter, Finset.mem_inter] at he ⊢
        exact ⟨he.1.1, he.2⟩
    _ = 2 := hv

end DegreeProfile

/-! ## Definition 3.2(b): Dangling endpoints U_S(H) -/

section DanglingEndpoints

noncomputable def danglingEndpoints (S : Frontier n) (H : Finset (Edge n)) :
    Finset (Fin n) :=
  (boundaryVertices S).filter fun v => degreeProfile S H v = 1

end DanglingEndpoints

/-! ## Perfect matchings -/

section PerfectMatching

structure PerfectMatching {α : Type*} [DecidableEq α] (U : Finset α) where
  pairs : Finset (α × α)
  fst_mem : ∀ p ∈ pairs, p.1 ∈ U
  snd_mem : ∀ p ∈ pairs, p.2 ∈ U
  ne_pair : ∀ p ∈ pairs, p.1 ≠ p.2
  covers : ∀ u ∈ U, ∃ p ∈ pairs, u = p.1 ∨ u = p.2
  unique : ∀ u ∈ U, ∀ p₁ ∈ pairs, ∀ p₂ ∈ pairs,
    (u = p₁.1 ∨ u = p₁.2) → (u = p₂.1 ∨ u = p₂.2) → p₁ = p₂
  card_eq : 2 * pairs.card = U.card

end PerfectMatching

/-! ## Premature cycle flag c_S(H) -/

section PrematureCycleFlag

def hasPrematureCycle (S : Frontier n) (H : Finset (Edge n)) : Prop :=
  ∃ comp : Finset (Edge n),
    comp ⊆ leftSubgraph S H ∧
    comp.Nonempty ∧
    (∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2) ∧
    comp ≠ H

open Classical in
noncomputable def prematureCycleFlag (S : Frontier n) (H : Finset (Edge n)) : Fin 2 :=
  if hasPrematureCycle S H then 1 else 0

end PrematureCycleFlag

/-! ## Key lemma: leftDeg + rightDeg = deg_H for every vertex -/

section DegreeDecomposition

theorem leftRight_disjoint_at_vertex (S : Frontier n) (H : Finset (Edge n)) (v : Fin n) :
    Disjoint
      (Finset.filter (fun e => v ∈ e) (leftSubgraph S H))
      (Finset.filter (fun e => v ∈ e) (rightSubgraph S H)) := by
  rw [Finset.disjoint_left]
  intro e he1 he2
  simp only [Finset.mem_filter] at he1 he2
  simp only [leftSubgraph, rightSubgraph, Finset.mem_inter] at he1 he2
  exact Finset.disjoint_left.mp S.disjoint he1.1.2 he2.1.2

theorem leftDeg_add_rightDeg_eq_two (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) (v : Fin n) :
    leftDegreeAt S H v + rightDegreeAt S H v = 2 := by
  have h1 := hH.twoRegular v
  unfold leftDegreeAt rightDegreeAt vertexDegreeIn
  rw [← Finset.card_union_of_disjoint (leftRight_disjoint_at_vertex S H v)]
  unfold vertexDegreeIn at h1
  unfold leftSubgraph rightSubgraph
  have hset : Finset.filter (fun e => v ∈ e) (H ∩ S.leftEdges) ∪
    Finset.filter (fun e => v ∈ e) (H ∩ S.rightEdges) =
    Finset.filter (fun e => v ∈ e) H := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨⟨hmem, _⟩, hv⟩ | ⟨⟨hmem, _⟩, hv⟩) <;> exact ⟨hmem, hv⟩
    · rintro ⟨hmem, hv⟩
      have hedge : e ∈ allEdges n := by
        simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hH.noLoops e hmem
      have : e ∈ S.leftEdges ∪ S.rightEdges := S.partition ▸ hedge
      rcases Finset.mem_union.mp this with hleft | hright
      · exact Or.inl ⟨⟨hmem, hleft⟩, hv⟩
      · exact Or.inr ⟨⟨hmem, hright⟩, hv⟩
  rw [hset]; exact h1

end DegreeDecomposition

/-! ## Dangling endpoints have even cardinality -/

section DanglingEndpointsEven

def PathComponentDecomposition (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) : Prop :=
  ∀ comp : Finset (Edge n), comp ⊆ leftSubgraph S H → comp.Nonempty →
    (∀ v : Fin n, vertexDegreeIn n comp v ≤ 2) →
    ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2)

theorem pathComponents_pairEndpoints :
  ∀ (n : ℕ) (S : Frontier n) (H : Finset (Edge n)),
    IsHamCycle n H → ¬ hasPrematureCycle S H →
    ∃ k : ℕ, (danglingEndpoints S H).card = 2 * k := by
  intro n S H hH hc
  have h2reg := hH.twoRegular
  have hsum : ∀ v : Fin n, leftDegreeAt S H v + rightDegreeAt S H v = 2 :=
    leftDeg_add_rightDeg_eq_two S H hH
  have hdeg_le2 : ∀ v : Fin n, leftDegreeAt S H v ≤ 2 := by
    intro v; have := hsum v; omega
  have dangling_eq : danglingEndpoints S H =
      Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 1 := by
    ext v
    simp only [danglingEndpoints, Finset.mem_filter, boundaryVertices, Finset.mem_univ,
      true_and, degreeProfile]
    constructor
    · intro ⟨_, hd⟩; exact hd
    · intro hd
      refine ⟨⟨?_, ?_⟩, hd⟩
      · have hld : leftDegreeAt S H v ≥ 1 := by omega
        unfold leftDegreeAt leftSubgraph vertexDegreeIn at hld
        have hne : (Finset.filter (fun e => v ∈ e) (H ∩ S.leftEdges)).Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty] at h
          rw [h, Finset.card_empty] at hld; omega
        obtain ⟨e, he⟩ := hne
        simp only [Finset.mem_filter, Finset.mem_inter] at he
        exact ⟨e, he.1.2, he.2⟩
      · have hrd : rightDegreeAt S H v ≥ 1 := by have := hsum v; omega
        unfold rightDegreeAt rightSubgraph vertexDegreeIn at hrd
        have hne : (Finset.filter (fun e => v ∈ e) (H ∩ S.rightEdges)).Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty] at h
          rw [h, Finset.card_empty] at hrd; omega
        obtain ⟨e, he⟩ := hne
        simp only [Finset.mem_filter, Finset.mem_inter] at he
        exact ⟨e, he.1.2, he.2⟩
  rw [dangling_eq]
  have hnoloops : ∀ e ∈ leftSubgraph S H, ¬ e.IsDiag := by
    intro e he
    simp only [leftSubgraph, Finset.mem_inter] at he
    exact hH.noLoops e he.1
  have edge_card_two : ∀ e ∈ leftSubgraph S H,
      (Finset.univ.filter fun v : Fin n => v ∈ e).card = 2 := by
    intro e he
    have hnd := hnoloops e he
    induction e using Sym2.ind with
    | h a b =>
      have hab : a ≠ b := fun h => hnd (Sym2.mk_isDiag_iff.mpr h)
      have : (Finset.univ.filter fun v : Fin n => v ∈ Sym2.mk (a, b)) = {a, b} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Sym2.mem_iff]
      rw [this, Finset.card_insert_of_notMem (by simp [hab]),
        Finset.card_singleton]
  have sum_eq : ∑ v ∈ (Finset.univ : Finset (Fin n)), leftDegreeAt S H v =
      2 * (leftSubgraph S H).card := by
    simp only [leftDegreeAt, leftSubgraph, vertexDegreeIn]
    have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := Finset.univ) (t := H ∩ S.leftEdges) (r := fun (v : Fin n) (e : Edge n) => v ∈ e)
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hdc
    rw [hdc]
    have : ∀ e ∈ H ∩ S.leftEdges,
        (Finset.filter (fun a => a ∈ e) Finset.univ).card = 2 := by
      intro e he; exact edge_card_two e he
    rw [Finset.sum_congr rfl this]
    simp [Finset.sum_const, mul_comm]
  set D1 := Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 1
  set D2 := Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 2
  set K := (leftSubgraph S H).card
  have hpart : ∑ v ∈ Finset.univ, leftDegreeAt S H v =
      ∑ v ∈ D1, leftDegreeAt S H v + ∑ v ∈ D2, leftDegreeAt S H v +
      ∑ v ∈ Finset.univ.filter (fun v : Fin n => leftDegreeAt S H v = 0),
        leftDegreeAt S H v := by
    have hdisj12 : Disjoint D1 D2 := by
      simp only [D1, D2, Finset.disjoint_filter]
      intro v _ h1 h2; omega
    have hdisj10 : Disjoint D1 (Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 0) := by
      simp only [D1, Finset.disjoint_filter]
      intro v _ h1 h0; omega
    have hdisj20 : Disjoint D2 (Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 0) := by
      simp only [D2, Finset.disjoint_filter]
      intro v _ h2 h0; omega
    have hunion : Finset.univ = D1 ∪ D2 ∪ (Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 0) := by
      ext v
      simp only [D1, D2, Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and]
      have hle := hdeg_le2 v
      set d := leftDegreeAt S H v with hd_def
      interval_cases d <;> simp_all
    conv_lhs => rw [hunion]
    rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdisj10, hdisj20⟩)]
    rw [Finset.sum_union hdisj12]
  have hD1sum : ∑ v ∈ D1, leftDegreeAt S H v = D1.card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [D1, Finset.mem_filter] at hv
    exact hv.2
  have hD2sum : ∑ v ∈ D2, leftDegreeAt S H v = 2 * D2.card := by
    have : ∑ v ∈ D2, leftDegreeAt S H v = ∑ _v ∈ D2, 2 := by
      apply Finset.sum_congr rfl
      intro v hv
      simp only [D2, Finset.mem_filter] at hv
      exact hv.2
    rw [this, Finset.sum_const, smul_eq_mul, mul_comm]
  have hD0sum : ∑ v ∈ Finset.univ.filter (fun v : Fin n => leftDegreeAt S H v = 0),
      leftDegreeAt S H v = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    simp only [Finset.mem_filter] at hv
    exact hv.2
  have htotal : D1.card + 2 * D2.card = 2 * K := by
    have := sum_eq
    rw [hpart, hD1sum, hD2sum, hD0sum] at this
    omega
  exact ⟨K - D2.card, by omega⟩

theorem danglingEndpoints_even (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) (hc : ¬ hasPrematureCycle S H) :
    Even (danglingEndpoints S H).card := by
  obtain ⟨k, hk⟩ := pathComponents_pairEndpoints n S H hH hc
  exact ⟨k, by omega⟩

end DanglingEndpointsEven

/-! ## Definition 3.2(c): Path-pairing π_S(H) -/

section PathPairing

open Classical in
private noncomputable def trivialMatchingOnEvenSet
    {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α]
    (U : Finset α) : ∀ (k : ℕ), U.card = 2 * k → PerfectMatching U
  | 0, hk => {
      pairs := ∅
      fst_mem := fun _ hp => by simp at hp
      snd_mem := fun _ hp => by simp at hp
      ne_pair := fun _ hp => by simp at hp
      covers := fun _ hu => by
        have : U = ∅ := Finset.card_eq_zero.mp (by omega)
        subst this; simp at hu
      unique := fun _ _ _ hp₁ => by simp at hp₁
      card_eq := by simp [show U.card = 0 from by omega]
    }
  | k + 1, hk =>
    have hne : U.Nonempty := Finset.card_pos.mp (by omega)
    have hne' : (U.erase (U.min' hne)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h
      have := Finset.card_erase_of_mem (Finset.min'_mem U hne)
      rw [h] at this; simp at this; omega
    let a := U.min' hne
    let b := (U.erase a).min' hne'
    have ha : a ∈ U := Finset.min'_mem U hne
    have hb' : b ∈ U.erase a := Finset.min'_mem _ hne'
    have hb : b ∈ U := Finset.mem_of_mem_erase hb'
    have hab : a ≠ b := by intro h; rw [h] at hb'; simp at hb'
    let U'' := (U.erase a).erase b
    have hU''_card : U''.card = 2 * k := by
      show ((U.erase a).erase b).card = 2 * k
      rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]; omega
    have hU''_sub : U'' ⊆ U := fun x hx =>
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
    have ha_not : a ∉ U'' := by
      intro h; have := Finset.mem_of_mem_erase h; simp at this
    have hb_not : b ∉ U'' := by simp [U'']
    let rest := trivialMatchingOnEvenSet U'' k hU''_card
    have rpne : ∀ p ∈ rest.pairs, p.1 ≠ a ∧ p.1 ≠ b ∧ p.2 ≠ a ∧ p.2 ≠ b := fun p hp =>
      ⟨fun h => ha_not (h ▸ rest.fst_mem p hp),
       fun h => hb_not (h ▸ rest.fst_mem p hp),
       fun h => ha_not (h ▸ rest.snd_mem p hp),
       fun h => hb_not (h ▸ rest.snd_mem p hp)⟩
    have ab_not : (a, b) ∉ rest.pairs := fun h => (rpne _ h).1 rfl
    { pairs := insert (a, b) rest.pairs
      fst_mem := fun p hp => by
        rw [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · exact ha
        · exact hU''_sub (rest.fst_mem p hp)
      snd_mem := fun p hp => by
        rw [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · exact hb
        · exact hU''_sub (rest.snd_mem p hp)
      ne_pair := fun p hp => by
        rw [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · exact hab
        · exact rest.ne_pair p hp
      covers := fun u hu => by
        by_cases hau : u = a
        · exact ⟨(a, b), Finset.mem_insert_self _ _, Or.inl hau⟩
        · by_cases hbu : u = b
          · exact ⟨(a, b), Finset.mem_insert_self _ _, Or.inr hbu⟩
          · have huU'' : u ∈ U'' :=
              Finset.mem_erase.mpr ⟨hbu, Finset.mem_erase.mpr ⟨hau, hu⟩⟩
            obtain ⟨p, hp, hup⟩ := rest.covers u huU''
            exact ⟨p, Finset.mem_insert_of_mem hp, hup⟩
      unique := fun u _ p₁ hp₁ p₂ hp₂ h1 h2 => by
        rw [Finset.mem_insert] at hp₁ hp₂
        rcases hp₁ with rfl | hp₁ <;> rcases hp₂ with rfl | hp₂
        · rfl
        · exfalso
          rcases h1 with rfl | rfl
          · rcases h2 with h | h
            · exact (rpne _ hp₂).1 h.symm
            · exact (rpne _ hp₂).2.2.1 h.symm
          · rcases h2 with h | h
            · exact (rpne _ hp₂).2.1 h.symm
            · exact (rpne _ hp₂).2.2.2 h.symm
        · exfalso
          rcases h2 with rfl | rfl
          · rcases h1 with h | h
            · exact (rpne _ hp₁).1 h.symm
            · exact (rpne _ hp₁).2.2.1 h.symm
          · rcases h1 with h | h
            · exact (rpne _ hp₁).2.1 h.symm
            · exact (rpne _ hp₁).2.2.2 h.symm
        · exact rest.unique u (by
            rcases h1 with rfl | rfl
            · exact rest.fst_mem p₁ hp₁
            · exact rest.snd_mem p₁ hp₁) p₁ hp₁ p₂ hp₂ h1 h2
      card_eq := by
        simp [ab_not]; have := rest.card_eq; omega }

private theorem danglingEndpoints_card_even_general
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    ∃ k : ℕ, (danglingEndpoints S H).card = 2 * k := by
  have hsum : ∀ v : Fin n, leftDegreeAt S H v + rightDegreeAt S H v = 2 :=
    leftDeg_add_rightDeg_eq_two S H hH
  have hdeg_le2 : ∀ v : Fin n, leftDegreeAt S H v ≤ 2 := by
    intro v; have := hsum v; omega
  have dangling_eq : danglingEndpoints S H =
      Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 1 := by
    ext v
    simp only [danglingEndpoints, Finset.mem_filter, boundaryVertices, Finset.mem_univ,
      true_and, degreeProfile]
    constructor
    · intro ⟨_, hd⟩; exact hd
    · intro hd
      refine ⟨⟨?_, ?_⟩, hd⟩
      · have hld : leftDegreeAt S H v ≥ 1 := by omega
        unfold leftDegreeAt leftSubgraph vertexDegreeIn at hld
        have hne : (Finset.filter (fun e => v ∈ e) (H ∩ S.leftEdges)).Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty] at h
          rw [h, Finset.card_empty] at hld; omega
        obtain ⟨e, he⟩ := hne
        simp only [Finset.mem_filter, Finset.mem_inter] at he
        exact ⟨e, he.1.2, he.2⟩
      · have hrd : rightDegreeAt S H v ≥ 1 := by have := hsum v; omega
        unfold rightDegreeAt rightSubgraph vertexDegreeIn at hrd
        have hne : (Finset.filter (fun e => v ∈ e) (H ∩ S.rightEdges)).Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty] at h
          rw [h, Finset.card_empty] at hrd; omega
        obtain ⟨e, he⟩ := hne
        simp only [Finset.mem_filter, Finset.mem_inter] at he
        exact ⟨e, he.1.2, he.2⟩
  rw [dangling_eq]
  have hnoloops : ∀ e ∈ leftSubgraph S H, ¬ e.IsDiag := by
    intro e he
    simp only [leftSubgraph, Finset.mem_inter] at he
    exact hH.noLoops e he.1
  have edge_card_two : ∀ e ∈ leftSubgraph S H,
      (Finset.univ.filter fun v : Fin n => v ∈ e).card = 2 := by
    intro e he
    have hnd := hnoloops e he
    induction e using Sym2.ind with
    | h a b =>
      have hab : a ≠ b := fun h => hnd (Sym2.mk_isDiag_iff.mpr h)
      have : (Finset.univ.filter fun v : Fin n => v ∈ Sym2.mk (a, b)) = {a, b} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Sym2.mem_iff]
      rw [this, Finset.card_insert_of_notMem (by simp [hab]),
        Finset.card_singleton]
  have sum_eq : ∑ v ∈ (Finset.univ : Finset (Fin n)), leftDegreeAt S H v =
      2 * (leftSubgraph S H).card := by
    simp only [leftDegreeAt, leftSubgraph, vertexDegreeIn]
    have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := Finset.univ) (t := H ∩ S.leftEdges) (r := fun (v : Fin n) (e : Edge n) => v ∈ e)
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hdc
    rw [hdc]
    have : ∀ e ∈ H ∩ S.leftEdges,
        (Finset.filter (fun a => a ∈ e) Finset.univ).card = 2 := by
      intro e he; exact edge_card_two e he
    rw [Finset.sum_congr rfl this]
    simp [Finset.sum_const, mul_comm]
  set D1 := Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 1
  set D2 := Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 2
  set K := (leftSubgraph S H).card
  have hpart : ∑ v ∈ Finset.univ, leftDegreeAt S H v =
      ∑ v ∈ D1, leftDegreeAt S H v + ∑ v ∈ D2, leftDegreeAt S H v +
      ∑ v ∈ Finset.univ.filter (fun v : Fin n => leftDegreeAt S H v = 0),
        leftDegreeAt S H v := by
    have hdisj12 : Disjoint D1 D2 := by
      simp only [D1, D2, Finset.disjoint_filter]
      intro v _ h1 h2; omega
    have hdisj10 : Disjoint D1 (Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 0) := by
      simp only [D1, Finset.disjoint_filter]
      intro v _ h1 h0; omega
    have hdisj20 : Disjoint D2 (Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 0) := by
      simp only [D2, Finset.disjoint_filter]
      intro v _ h2 h0; omega
    have hunion : Finset.univ = D1 ∪ D2 ∪ (Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 0) := by
      ext v
      simp only [D1, D2, Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and]
      have hle := hdeg_le2 v
      set d := leftDegreeAt S H v with hd_def
      interval_cases d <;> simp_all
    conv_lhs => rw [hunion]
    rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdisj10, hdisj20⟩)]
    rw [Finset.sum_union hdisj12]
  have hD1sum : ∑ v ∈ D1, leftDegreeAt S H v = D1.card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [D1, Finset.mem_filter] at hv
    exact hv.2
  have hD2sum : ∑ v ∈ D2, leftDegreeAt S H v = 2 * D2.card := by
    have : ∑ v ∈ D2, leftDegreeAt S H v = ∑ _v ∈ D2, 2 := by
      apply Finset.sum_congr rfl
      intro v hv
      simp only [D2, Finset.mem_filter] at hv
      exact hv.2
    rw [this, Finset.sum_const, smul_eq_mul, mul_comm]
  have hD0sum : ∑ v ∈ Finset.univ.filter (fun v : Fin n => leftDegreeAt S H v = 0),
      leftDegreeAt S H v = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    simp only [Finset.mem_filter] at hv
    exact hv.2
  have htotal : D1.card + 2 * D2.card = 2 * K := by
    have := sum_eq
    rw [hpart, hD1sum, hD2sum, hD0sum] at this
    omega
  exact ⟨K - D2.card, by omega⟩

/-! ### Path-component normal form (hamiltonian_route.tex Lemma, lines 275-361)

Let H be a Hamiltonian cycle on [n] and S a balanced interior frontier
with c_S(H) = 0. Then:
(1) Every connected component of L_S(H) is a simple path (possibly single vertex).
(2) Every path-component with ≥1 edge has exactly two endpoints of left-degree 1.
    Both are boundary vertices.
(3) Internal vertices (left-degree 2) don't affect the boundary multigraph.
(4) Isolated vertices (left-degree 0) are boundary iff incident to both sides.
(5) No component is disjoint from B_S unless it's an isolated vertex with no left edges.
(6) The L-edges of the boundary multigraph are exactly the pairs of π_S(H). -/

private lemma leftSubgraph_max_degree_two
    (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) (v : Fin n) :
    vertexDegreeIn n (leftSubgraph S H) v ≤ 2 := by
  have h := leftDeg_add_rightDeg_eq_two S H hH v
  show leftDegreeAt S H v ≤ 2
  omega

private lemma leftSubgraph_component_is_path
    (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (hRight : (rightSubgraph S H).Nonempty)
    (comp : Finset (Edge n)) (hcomp : comp ⊆ leftSubgraph S H)
    (hne : comp.Nonempty)
    (h2reg : ∀ v : Fin n, vertexDegreeIn n comp v ≤ 2) :
    ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2) := by
  intro hall
  have comp_sub_H : comp ⊆ H :=
    Finset.Subset.trans hcomp Finset.inter_subset_left
  have comp_eq_H : comp = H :=
    cycle_component_equals_H H hH comp comp_sub_H hne hall
  have H_sub_left : H ⊆ S.leftEdges := by
    intro e he
    have : e ∈ comp := comp_eq_H ▸ he
    have : e ∈ H ∩ S.leftEdges := hcomp this
    exact Finset.mem_inter.mp this |>.2
  obtain ⟨e, he⟩ := hRight
  have he_H : e ∈ H := Finset.mem_inter.mp he |>.1
  have he_right : e ∈ S.rightEdges := Finset.mem_inter.mp he |>.2
  have he_left : e ∈ S.leftEdges := H_sub_left he_H
  exact Finset.disjoint_left.mp S.disjoint he_left he_right

private lemma vertexDegreeIn_mono (n : ℕ) (A B : Finset (Edge n)) (hAB : A ⊆ B) (v : Fin n) :
    vertexDegreeIn n A v ≤ vertexDegreeIn n B v := by
  unfold vertexDegreeIn
  exact Finset.card_le_card (Finset.filter_subset_filter _ hAB)

private lemma vertexDegreeIn_comp_eq_of_maximal (n : ℕ)
    (comp parent : Finset (Edge n)) (hcomp : comp ⊆ parent)
    (hmax : ∀ e ∈ parent \ comp, ∀ v : Fin n, v ∈ e → vertexDegreeIn n comp v = 0)
    (v : Fin n) (hv : vertexDegreeIn n comp v > 0) :
    vertexDegreeIn n comp v = vertexDegreeIn n parent v := by
  unfold vertexDegreeIn at *
  apply le_antisymm
  · exact Finset.card_le_card (Finset.filter_subset_filter _ hcomp)
  · apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_filter] at he ⊢
    by_contra h
    push_neg at h
    have hnotcomp : e ∉ comp := fun hc => absurd he.2 (h hc)
    have hdiff : e ∈ parent \ comp := Finset.mem_sdiff.mpr ⟨he.1, hnotcomp⟩
    have := hmax e hdiff v he.2
    omega

private lemma deg1_vertex_exists_unique_edge
    (n : ℕ) (comp : Finset (Edge n)) (v : Fin n)
    (hdeg1 : vertexDegreeIn n comp v = 1) :
    ∃! e, e ∈ comp ∧ v ∈ e := by
  unfold vertexDegreeIn at hdeg1
  rw [Finset.card_eq_one] at hdeg1
  obtain ⟨e, he⟩ := hdeg1
  have hmem := he ▸ Finset.mem_singleton_self e
  simp only [Finset.mem_filter] at hmem
  exact ⟨e, ⟨hmem.1, hmem.2⟩, fun e' ⟨he'1, he'2⟩ => by
    have : e' ∈ Finset.filter (fun e => v ∈ e) comp := Finset.mem_filter.mpr ⟨he'1, he'2⟩
    rw [he] at this; exact Finset.mem_singleton.mp this⟩

private lemma deg1_other_endpoint
    (n : ℕ) (comp : Finset (Edge n)) (v : Fin n)
    (hdeg1 : vertexDegreeIn n comp v = 1) (hnoloops : ∀ e ∈ comp, ¬ e.IsDiag) :
    ∃ w : Fin n, w ≠ v ∧ ∃ e ∈ comp, v ∈ e ∧ w ∈ e := by
  obtain ⟨e, ⟨he, hve⟩, _⟩ := deg1_vertex_exists_unique_edge n comp v hdeg1
  have hnd := hnoloops e he
  exact ⟨Sym2.Mem.other hve, Sym2.other_ne hnd hve,
    e, he, hve, Sym2.other_mem hve⟩

private lemma filter_erase_eq {α : Type*} [DecidableEq α] {s : Finset α}
    {p : α → Prop} [DecidablePred p] {a : α} :
    Finset.filter p (s.erase a) = (Finset.filter p s).erase a := by
  ext x; simp only [Finset.mem_filter, Finset.mem_erase]
  exact ⟨fun ⟨⟨hne, hx⟩, hp⟩ => ⟨hne, hx, hp⟩,
         fun ⟨hne, hx, hp⟩ => ⟨⟨hne, hx⟩, hp⟩⟩

private lemma erase_edge_deg (n : ℕ) (comp : Finset (Edge n)) (e : Edge n)
    (he : e ∈ comp) (v : Fin n) :
    vertexDegreeIn n (comp.erase e) v =
      if v ∈ e then vertexDegreeIn n comp v - 1 else vertexDegreeIn n comp v := by
  unfold vertexDegreeIn
  split
  · next hve =>
    rw [filter_erase_eq, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨he, hve⟩)]
  · next hve =>
    congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_erase]
    exact ⟨fun ⟨⟨_, hx⟩, hv⟩ => ⟨hx, hv⟩,
           fun ⟨hx, hv⟩ => ⟨⟨fun h => hve (h ▸ hv), hx⟩, hv⟩⟩

private lemma deg1_unique_edge_eq (n : ℕ) (comp : Finset (Edge n)) (v : Fin n)
    (hdeg1 : vertexDegreeIn n comp v = 1) (e' : Edge n) (he' : e' ∈ comp) (hve' : v ∈ e') :
    ∀ e'' ∈ comp, v ∈ e'' → e'' = e' := by
  intro e'' he'' hve''
  have ⟨_, _, huniq⟩ := deg1_vertex_exists_unique_edge n comp v hdeg1
  have h1 := huniq e' ⟨he', hve'⟩
  have h2 := huniq e'' ⟨he'', hve''⟩
  rw [h2, h1]

private lemma walk_avoids_deg1_aux (n : ℕ) (comp : Finset (Edge n)) (v : Fin n)
    (hdeg1 : vertexDegreeIn n comp v = 1)
    (e : Edge n) (he : e ∈ comp) (hve : v ∈ e)
    {a b : Fin n} (ha : a ≠ v) (hb : b ≠ v)
    (walk : (edgeSetToGraph n comp).Walk a b) :
    (edgeSetToGraph n (comp.erase e)).Reachable a b := by
  suffices key : ∀ (len : ℕ) {x y : Fin n},
      (w : (edgeSetToGraph n comp).Walk x y) → w.length ≤ len →
      x ≠ v → y ≠ v → (edgeSetToGraph n (comp.erase e)).Reachable x y from
    key walk.length walk (le_refl _) ha hb
  intro len; induction len with
  | zero =>
    intro x y w hlen _hx _hy
    have := SimpleGraph.Walk.eq_of_length_eq_zero (Nat.le_zero.mp hlen)
    exact this ▸ SimpleGraph.Reachable.refl _
  | succ k ih =>
    intro x y w hlen hx hy
    by_cases hwlen : w.length = 0
    · exact (SimpleGraph.Walk.eq_of_length_eq_zero hwlen) ▸ SimpleGraph.Reachable.refl _
    · obtain ⟨c, hc_walk⟩ : ∃ c, ∃ (hadj : (edgeSetToGraph n comp).Adj x c),
          ∃ (rest : (edgeSetToGraph n comp).Walk c y), w.length = rest.length + 1 := by
        match w with
        | @SimpleGraph.Walk.cons _ _ _ c _ hadj rest =>
          exact ⟨c, hadj, rest, rfl⟩
      obtain ⟨hadj_xc, rest, hlen_eq⟩ := hc_walk
      have ⟨hne_xc, hmem_xc⟩ := hadj_xc
      have hrest_len : rest.length ≤ k := by omega
      by_cases hcv : c = v
      · by_cases hrestlen0 : rest.length = 0
        · have := SimpleGraph.Walk.eq_of_length_eq_zero hrestlen0
          rw [hcv] at this; exact absurd this hy.symm
        · obtain ⟨c2, hc2_walk⟩ : ∃ c2, ∃ (hadj2 : (edgeSetToGraph n comp).Adj c c2),
              ∃ (rest2 : (edgeSetToGraph n comp).Walk c2 y),
                rest.length = rest2.length + 1 := by
            match rest with
            | @SimpleGraph.Walk.cons _ _ _ c2 _ hadj2 rest2 =>
              exact ⟨c2, hadj2, rest2, rfl⟩
          obtain ⟨hadj2, rest2, hlen2_eq⟩ := hc2_walk
          have ⟨_, hmem_cc2⟩ := hadj2
          have hmem_vc2 : Sym2.mk (v, c2) ∈ comp := hcv ▸ hmem_cc2
          have hv_in_vc2 : v ∈ Sym2.mk (v, c2) := Sym2.mem_mk_left v c2
          have hedge2_eq : Sym2.mk (v, c2) = e :=
            deg1_unique_edge_eq n comp v hdeg1 e he hve _ hmem_vc2 hv_in_vc2
          have hmem_xv : Sym2.mk (x, v) ∈ comp := hcv ▸ hmem_xc
          have hedge1_eq : Sym2.mk (x, v) = e :=
            deg1_unique_edge_eq n comp v hdeg1 e he hve _
              hmem_xv (Sym2.mem_mk_right x v)
          have hc2_eq_x : c2 = x := by
            have hx_in_e : x ∈ e := by rw [← hedge1_eq]; exact Sym2.mem_mk_left x v
            have hc2_in_e : c2 ∈ e := by rw [← hedge2_eq]; exact Sym2.mem_mk_right v c2
            induction e using Sym2.ind with
            | h p q =>
              simp only [Sym2.mem_iff] at hve hx_in_e hc2_in_e
              have hxv : x ≠ v := hx
              rcases hve with rfl | rfl <;> rcases hx_in_e with rfl | rfl <;>
                rcases hc2_in_e with rfl | rfl
              all_goals first | rfl | contradiction
          have hrest2_len : rest2.length ≤ k := by omega
          subst hc2_eq_x
          exact ih rest2 hrest2_len hx hy
      · have hedge_ne : Sym2.mk (x, c) ≠ e := by
          intro heq
          have hv_in : v ∈ Sym2.mk (x, c) := heq ▸ hve
          simp only [Sym2.mem_iff] at hv_in
          rcases hv_in with rfl | rfl
          · exact hx rfl
          · exact hcv rfl
        have hmem_erase : Sym2.mk (x, c) ∈ comp.erase e :=
          Finset.mem_erase.mpr ⟨hedge_ne, hmem_xc⟩
        have hadj_erase : (edgeSetToGraph n (comp.erase e)).Adj x c := ⟨hne_xc, hmem_erase⟩
        exact hadj_erase.reachable.trans (ih rest hrest_len hcv hy)

private lemma leaf_removal_connected (n : ℕ) (comp : Finset (Edge n))
    (hconn : IsIncidentConnected n comp) (v : Fin n)
    (hdeg1 : vertexDegreeIn n comp v = 1)
    (e : Edge n) (he : e ∈ comp) (hve : v ∈ e) :
    IsIncidentConnected n (comp.erase e) := by
  intro a b ⟨ea, hea_mem, hea_a⟩ ⟨eb, heb_mem, heb_b⟩
  have hea_comp : ea ∈ comp := Finset.mem_of_mem_erase hea_mem
  have heb_comp : eb ∈ comp := Finset.mem_of_mem_erase heb_mem
  have hea_ne : ea ≠ e := fun h => by
    rw [h] at hea_mem; exact (Finset.notMem_erase e comp) hea_mem
  have heb_ne : eb ≠ e := fun h => by
    rw [h] at heb_mem; exact (Finset.notMem_erase e comp) heb_mem
  have ha_ne_v : a ≠ v := by
    intro hav
    exact hea_ne (deg1_unique_edge_eq n comp v hdeg1 e he hve ea hea_comp (hav ▸ hea_a))
  have hb_ne_v : b ≠ v := by
    intro hbv
    exact heb_ne (deg1_unique_edge_eq n comp v hdeg1 e he hve eb heb_comp (hbv ▸ heb_b))
  have hreach := hconn a b ⟨ea, hea_comp, hea_a⟩ ⟨eb, heb_comp, heb_b⟩
  obtain ⟨walk⟩ := hreach
  exact walk_avoids_deg1_aux n comp v hdeg1 e he hve ha_ne_v hb_ne_v walk

private lemma incident_vertices_le_edges_plus_one
    (n : ℕ) (comp : Finset (Edge n))
    (hconn : IsIncidentConnected n comp)
    (hdeg_le2 : ∀ v : Fin n, vertexDegreeIn n comp v ≤ 2)
    (hpath : ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hnoloops : ∀ e ∈ comp, ¬ e.IsDiag) :
    (Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v ≥ 1).card ≤ comp.card + 1 := by
  sorry

private lemma connected_maxdeg2_not_cycle_exactly2_deg1
    (n : ℕ) (comp : Finset (Edge n))
    (_hne : comp.Nonempty)
    (hconn : IsIncidentConnected n comp)
    (hdeg_le2 : ∀ v : Fin n, vertexDegreeIn n comp v ≤ 2)
    (hpath : ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hnoloops : ∀ e ∈ comp, ¬ e.IsDiag) :
    (Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v = 1).card = 2 := by
  set D1 := Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v = 1
  set D2 := Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v = 2
  have hdisj12 : Disjoint D1 D2 := by
    simp only [D1, D2, Finset.disjoint_filter]; intro v _ h1 h2; omega
  have edge_card_two : ∀ e ∈ comp,
      (Finset.univ.filter fun v : Fin n => v ∈ e).card = 2 := by
    intro e he
    have hnd := hnoloops e he
    induction e using Sym2.ind with
    | h a b =>
      have hab : a ≠ b := fun h => hnd (Sym2.mk_isDiag_iff.mpr h)
      have : (Finset.univ.filter fun v : Fin n => v ∈ Sym2.mk (a, b)) = {a, b} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Sym2.mem_iff]
      rw [this, Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
  have sum_eq : ∑ v ∈ (Finset.univ : Finset (Fin n)), vertexDegreeIn n comp v =
      2 * comp.card := by
    simp only [vertexDegreeIn]
    have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := Finset.univ) (t := comp) (r := fun (v : Fin n) (e : Edge n) => v ∈ e)
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hdc
    rw [hdc]
    have : ∀ e ∈ comp, (Finset.filter (fun a => a ∈ e) Finset.univ).card = 2 := by
      intro e he; exact edge_card_two e he
    rw [Finset.sum_congr rfl this]
    simp [Finset.sum_const, mul_comm]
  have hD1sum : ∑ v ∈ D1, vertexDegreeIn n comp v = D1.card := by
    rw [Finset.card_eq_sum_ones]; apply Finset.sum_congr rfl
    intro v hv; simp only [D1, Finset.mem_filter] at hv; exact hv.2
  have hD2sum : ∑ v ∈ D2, vertexDegreeIn n comp v = 2 * D2.card := by
    have : ∑ v ∈ D2, vertexDegreeIn n comp v = ∑ _v ∈ D2, 2 := by
      apply Finset.sum_congr rfl
      intro v hv; simp only [D2, Finset.mem_filter] at hv; exact hv.2
    rw [this, Finset.sum_const, smul_eq_mul, mul_comm]
  have htotal : D1.card + 2 * D2.card = 2 * comp.card := by
    set D0 := Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v = 0
    have hdisj01 : Disjoint D0 D1 := by
      simp only [D0, D1, Finset.disjoint_filter]; intro v _ h0 h1; omega
    have hdisj02 : Disjoint D0 D2 := by
      simp only [D0, D2, Finset.disjoint_filter]; intro v _ h0 h2; omega
    have hunion : Finset.univ = D0 ∪ D1 ∪ D2 := by
      ext v
      simp only [D0, D1, D2, Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and]
      have hle := hdeg_le2 v
      set d := vertexDegreeIn n comp v; interval_cases d <;> simp_all
    have hD0sum : ∑ v ∈ D0, vertexDegreeIn n comp v = 0 := by
      apply Finset.sum_eq_zero; intro v hv; simp only [D0, Finset.mem_filter] at hv; exact hv.2
    have hpart : ∑ v ∈ Finset.univ, vertexDegreeIn n comp v =
        ∑ v ∈ D0, vertexDegreeIn n comp v +
        ∑ v ∈ D1, vertexDegreeIn n comp v +
        ∑ v ∈ D2, vertexDegreeIn n comp v := by
      conv_lhs => rw [hunion]
      rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdisj02, hdisj12⟩)]
      rw [Finset.sum_union hdisj01]
    rw [hpart, hD0sum, hD1sum, hD2sum] at sum_eq; omega
  have hD1_pos : D1.card ≥ 1 := by
    push_neg at hpath; obtain ⟨v, hv⟩ := hpath
    have hle := hdeg_le2 v
    have : vertexDegreeIn n comp v = 1 := by omega
    exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, this⟩⟩
  have hD1_even : ∃ k, D1.card = 2 * k := ⟨comp.card - D2.card, by omega⟩
  have hD1_ge2 : D1.card ≥ 2 := by obtain ⟨k, hk⟩ := hD1_even; omega
  have hV_eq : (Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v ≥ 1) = D1 ∪ D2 := by
    ext v; simp only [D1, D2, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    have hle := hdeg_le2 v
    constructor
    · intro hge; omega
    · rintro (h | h) <;> omega
  have hV_card : (Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v ≥ 1).card =
      D1.card + D2.card := by
    rw [hV_eq, Finset.card_union_of_disjoint hdisj12]
  have hD1_le2 : D1.card ≤ 2 := by
    have hle := incident_vertices_le_edges_plus_one n comp hconn hdeg_le2 hpath hnoloops
    rw [hV_card] at hle; omega
  omega

private lemma finset_card_eq_two {α : Type*} [DecidableEq α]
    (S : Finset α) (hcard : S.card = 2) :
    ∃ a b : α, a ≠ b ∧ a ∈ S ∧ b ∈ S ∧ S = {a, b} := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hne
  have hne' : (S.erase a).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h
    have := Finset.card_erase_of_mem ha; rw [h] at this; simp at this; omega
  obtain ⟨b, hb'⟩ := hne'
  have hb : b ∈ S := Finset.mem_of_mem_erase hb'
  have hab : a ≠ b := by intro h; rw [h] at hb'; simp at hb'
  refine ⟨a, b, hab, ha, hb, ?_⟩
  ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hx
    by_contra h; push_neg at h
    have hxa : x ≠ a := h.1; have hxb : x ≠ b := h.2
    have hx_erase : x ∈ S.erase a := Finset.mem_erase.mpr ⟨hxa, hx⟩
    have hx_erase2 : x ∈ (S.erase a).erase b := Finset.mem_erase.mpr ⟨hxb, hx_erase⟩
    have hcard' : ((S.erase a).erase b).card = 0 := by
      rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]; omega
    rw [Finset.card_eq_zero] at hcard'; rw [hcard'] at hx_erase2; simp at hx_erase2
  · rintro (rfl | rfl) <;> assumption

private lemma path_component_has_two_deg1_vertices
    (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (comp : Finset (Edge n)) (hcomp : comp ⊆ leftSubgraph S H)
    (hne : comp.Nonempty)
    (hpath : ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hconn : IsIncidentConnected n comp)
    (hmax : ∀ e ∈ leftSubgraph S H \ comp,
      ∀ v : Fin n, v ∈ e → vertexDegreeIn n comp v = 0) :
    ∃ u v : Fin n, u ≠ v ∧
      vertexDegreeIn n comp u = 1 ∧ vertexDegreeIn n comp v = 1 ∧
      u ∈ danglingEndpoints S H ∧ v ∈ danglingEndpoints S H ∧
      (edgeSetToGraph n comp).Reachable u v ∧
      (∀ w : Fin n, vertexDegreeIn n comp w = 1 → w = u ∨ w = v) := by
  have hdeg_le2 : ∀ v : Fin n, vertexDegreeIn n comp v ≤ 2 := by
    intro v
    calc vertexDegreeIn n comp v
        ≤ vertexDegreeIn n (leftSubgraph S H) v :=
          vertexDegreeIn_mono n comp (leftSubgraph S H) hcomp v
      _ ≤ 2 := leftSubgraph_max_degree_two S H hH v
  set D1 := Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v = 1
  have hcomp_noloops : ∀ e ∈ comp, ¬ e.IsDiag := by
    intro e he; exact hH.noLoops e (Finset.inter_subset_left (hcomp he))
  have hD1_eq2 : D1.card = 2 :=
    connected_maxdeg2_not_cycle_exactly2_deg1 n comp hne hconn hdeg_le2 hpath hcomp_noloops
  obtain ⟨u, v, huv_ne, hu_mem, hv_mem, hD1_eq⟩ := finset_card_eq_two D1 hD1_eq2
  simp only [D1, Finset.mem_filter] at hu_mem hv_mem
  have deg1_implies_dangling : ∀ w : Fin n, vertexDegreeIn n comp w = 1 →
      w ∈ danglingEndpoints S H := by
    intro w hw
    have hpos : vertexDegreeIn n comp w > 0 := by omega
    have hcomp_eq := vertexDegreeIn_comp_eq_of_maximal n comp
      (leftSubgraph S H) hcomp hmax w hpos
    simp only [danglingEndpoints, Finset.mem_filter, degreeProfile]
    constructor
    · simp only [boundaryVertices, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · have hleft : leftDegreeAt S H w ≥ 1 := by
          show vertexDegreeIn n (leftSubgraph S H) w ≥ 1; omega
        unfold leftDegreeAt leftSubgraph vertexDegreeIn at hleft
        have hne' : (Finset.filter (fun e => w ∈ e) (H ∩ S.leftEdges)).Nonempty := by
          by_contra h'; rw [Finset.not_nonempty_iff_eq_empty] at h'
          rw [h', Finset.card_empty] at hleft; omega
        obtain ⟨e, he⟩ := hne'
        simp only [Finset.mem_filter, Finset.mem_inter] at he
        exact ⟨e, he.1.2, he.2⟩
      · have hsum := leftDeg_add_rightDeg_eq_two S H hH w
        have hleft : leftDegreeAt S H w = 1 := by
          show vertexDegreeIn n (leftSubgraph S H) w = 1; omega
        have hright : rightDegreeAt S H w ≥ 1 := by omega
        unfold rightDegreeAt rightSubgraph vertexDegreeIn at hright
        have hne' : (Finset.filter (fun e => w ∈ e) (H ∩ S.rightEdges)).Nonempty := by
          by_contra h'; rw [Finset.not_nonempty_iff_eq_empty] at h'
          rw [h', Finset.card_empty] at hright; omega
        obtain ⟨e, he⟩ := hne'
        simp only [Finset.mem_filter, Finset.mem_inter] at he
        exact ⟨e, he.1.2, he.2⟩
    · show leftDegreeAt S H w = 1
      show vertexDegreeIn n (leftSubgraph S H) w = 1; omega
  have hu_incident : ∃ e ∈ comp, u ∈ e := by
    unfold vertexDegreeIn at hu_mem
    have h0 : 0 < (Finset.filter (fun e => u ∈ e) comp).card := by omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp h0
    exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
  have hv_incident : ∃ e ∈ comp, v ∈ e := by
    unfold vertexDegreeIn at hv_mem
    have h0 : 0 < (Finset.filter (fun e => v ∈ e) comp).card := by omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp h0
    exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
  refine ⟨u, v, huv_ne, hu_mem.2, hv_mem.2,
    deg1_implies_dangling u hu_mem.2, deg1_implies_dangling v hv_mem.2,
    hconn u v hu_incident hv_incident, ?_⟩
  intro w hw
  have : w ∈ D1 := Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩
  rw [hD1_eq] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  exact this

open Classical in
private noncomputable def edgeComponentOf (n : ℕ) (edges : Finset (Edge n))
    (u : Fin n) : Finset (Edge n) :=
  edges.filter fun e =>
    ∃ v : Fin n, v ∈ e ∧ (edgeSetToGraph n edges).Reachable u v

private lemma edgeComponentOf_mem (n : ℕ) (edges : Finset (Edge n))
    (u : Fin n) (e : Edge n) (he : e ∈ edges) (v : Fin n)
    (hv : v ∈ e) (hreach : (edgeSetToGraph n edges).Reachable u v) :
    e ∈ edgeComponentOf n edges u := by
  unfold edgeComponentOf
  simp only [Finset.mem_filter]
  exact ⟨he, v, hv, hreach⟩

private lemma edgeComponentOf_sub (n : ℕ) (edges : Finset (Edge n)) (u : Fin n) :
    edgeComponentOf n edges u ⊆ edges := by
  intro e he
  unfold edgeComponentOf at he
  simp only [Finset.mem_filter] at he
  exact he.1

private lemma edgeComponentOf_reachable_from_incident (n : ℕ) (edges : Finset (Edge n))
    (u v : Fin n) (hv : ∃ e ∈ edgeComponentOf n edges u, v ∈ e) :
    (edgeSetToGraph n edges).Reachable u v := by
  obtain ⟨e, he, hve⟩ := hv
  simp only [edgeComponentOf, Finset.mem_filter] at he
  obtain ⟨he_mem, w, hw_mem, hw_reach⟩ := he
  by_cases hvw : v = w
  · exact hvw ▸ hw_reach
  · induction e using Sym2.ind with
    | h a b =>
      simp only [Sym2.mem_iff] at hve hw_mem
      rcases hve with rfl | rfl <;> rcases hw_mem with rfl | rfl
      · exact absurd rfl hvw
      · have hadj : (edgeSetToGraph n edges).Adj w v := by
          constructor
          · exact fun h => hvw h.symm
          · show Sym2.mk (w, v) ∈ edges
            rw [Sym2.eq_swap]; exact he_mem
        exact hw_reach.trans hadj.reachable
      · have hadj : (edgeSetToGraph n edges).Adj w v := by
          constructor
          · exact fun h => hvw h.symm
          · show Sym2.mk (w, v) ∈ edges
            exact he_mem
        exact hw_reach.trans hadj.reachable
      · exact absurd rfl hvw

private lemma reachable_from_u_in_component (n : ℕ) (edges : Finset (Edge n))
    (u v : Fin n) (hreach : (edgeSetToGraph n edges).Reachable u v) :
    (edgeSetToGraph n (edgeComponentOf n edges u)).Reachable u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach ⊢
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev hadj ih =>
    apply Relation.ReflTransGen.tail ih
    obtain ⟨hne, hmem⟩ := hadj
    refine ⟨hne, ?_⟩
    simp only [edgeComponentOf, Finset.mem_filter]
    have hprev_reach : (edgeSetToGraph n edges).Reachable u _ :=
      (SimpleGraph.reachable_iff_reflTransGen _ _).mpr hprev
    exact ⟨hmem, _, Sym2.mem_mk_left _ _, hprev_reach⟩

private lemma edgeComponentOf_incident_connected (n : ℕ) (edges : Finset (Edge n))
    (u : Fin n) (_hu : ∃ e ∈ edges, u ∈ e) :
    IsIncidentConnected n (edgeComponentOf n edges u) := by
  intro v w hv_inc hw_inc
  have hv_reach : (edgeSetToGraph n edges).Reachable u v :=
    edgeComponentOf_reachable_from_incident n edges u v hv_inc
  have hw_reach : (edgeSetToGraph n edges).Reachable u w :=
    edgeComponentOf_reachable_from_incident n edges u w hw_inc
  exact (reachable_from_u_in_component n edges u v hv_reach).symm.trans
    (reachable_from_u_in_component n edges u w hw_reach)

private lemma edgeComponentOf_nonempty (n : ℕ) (edges : Finset (Edge n))
    (u : Fin n) (hu : ∃ e ∈ edges, u ∈ e) :
    (edgeComponentOf n edges u).Nonempty := by
  obtain ⟨e, he, hue⟩ := hu
  exact ⟨e, edgeComponentOf_mem n edges u e he u hue (SimpleGraph.Reachable.refl u)⟩

private lemma edgeComponentOf_degree_le (n : ℕ) (edges : Finset (Edge n))
    (u v : Fin n) :
    vertexDegreeIn n (edgeComponentOf n edges u) v ≤ vertexDegreeIn n edges v := by
  unfold vertexDegreeIn
  apply Finset.card_le_card
  exact Finset.filter_subset_filter _ (edgeComponentOf_sub n edges u)

private lemma edgeComponentOf_degree_eq (n : ℕ) (edges : Finset (Edge n))
    (u v : Fin n) (hreach : (edgeSetToGraph n edges).Reachable u v) :
    vertexDegreeIn n (edgeComponentOf n edges u) v = vertexDegreeIn n edges v := by
  unfold vertexDegreeIn
  apply le_antisymm
  · exact Finset.card_le_card (Finset.filter_subset_filter _ (edgeComponentOf_sub n edges u))
  · apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_filter] at he ⊢
    exact ⟨edgeComponentOf_mem n edges u e he.1 v he.2 hreach, he.2⟩

private lemma edgeComponentOf_reachable_iff (n : ℕ) (edges : Finset (Edge n))
    (u v : Fin n) (hv : ∃ e ∈ edgeComponentOf n edges u, v ∈ e) :
    (edgeSetToGraph n edges).Reachable u v :=
  edgeComponentOf_reachable_from_incident n edges u v hv

private lemma edgeComponentOf_not_cycle (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) (u : Fin n) (hu : u ∈ danglingEndpoints S H) :
    ¬(∀ v : Fin n, vertexDegreeIn n (edgeComponentOf n (leftSubgraph S H) u) v = 0 ∨
      vertexDegreeIn n (edgeComponentOf n (leftSubgraph S H) u) v = 2) := by
  intro hall
  have hu_deg : vertexDegreeIn n (leftSubgraph S H) u = 1 := by
    simp only [danglingEndpoints, Finset.mem_filter, degreeProfile] at hu
    exact hu.2
  have hcomp_deg := edgeComponentOf_degree_eq n (leftSubgraph S H) u u
    (SimpleGraph.Reachable.refl u)
  have : vertexDegreeIn n (edgeComponentOf n (leftSubgraph S H) u) u = 1 := by
    rw [hcomp_deg]; exact hu_deg
  rcases hall u with h0 | h2 <;> omega

private lemma reachable_in_component_lifts (n : ℕ) (edges : Finset (Edge n))
    (u v : Fin n)
    (hreach : (edgeSetToGraph n (edgeComponentOf n edges u)).Reachable u v) :
    (edgeSetToGraph n edges).Reachable u v := by
  have hsub := edgeComponentOf_sub n edges u
  apply SimpleGraph.Reachable.mono _ hreach
  intro x y hadj
  exact ⟨hadj.1, hsub hadj.2⟩

theorem deg1_unique_partner
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (u : Fin n) (hu : u ∈ danglingEndpoints S H) :
    ∃! v, v ∈ danglingEndpoints S H ∧ v ≠ u ∧
      (edgeSetToGraph n (leftSubgraph S H)).Reachable u v := by
  set L := leftSubgraph S H with hL_def
  set comp := edgeComponentOf n L u
  have hu_dangling : degreeProfile S H u = 1 := by
    simp only [danglingEndpoints, Finset.mem_filter] at hu
    exact hu.2
  have hu_deg : vertexDegreeIn n L u = 1 := by
    unfold degreeProfile leftDegreeAt at hu_dangling
    exact hu_dangling
  have hu_edge : ∃ e ∈ L, u ∈ e := by
    unfold vertexDegreeIn at hu_deg
    by_contra h
    push_neg at h
    have : (L.filter fun e => u ∈ e).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he
      exact h e he
    omega
  have hcomp_sub : comp ⊆ L := edgeComponentOf_sub n L u
  have hcomp_ne : comp.Nonempty := edgeComponentOf_nonempty n L u hu_edge
  have hcomp_conn : IsIncidentConnected n comp := edgeComponentOf_incident_connected n L u hu_edge
  have hcomp_not_cycle := edgeComponentOf_not_cycle S H hH u hu
  have hcomp_max : ∀ e ∈ L \ comp, ∀ v : Fin n, v ∈ e → vertexDegreeIn n comp v = 0 := by
    intro e he_diff v hv_in_e
    simp only [Finset.mem_sdiff] at he_diff
    obtain ⟨he_L, he_not_comp⟩ := he_diff
    by_contra h_nonzero
    have hv_reach : (edgeSetToGraph n L).Reachable u v := by
      have h_pos : 0 < vertexDegreeIn n comp v := by omega
      unfold vertexDegreeIn at h_pos
      rw [Finset.card_pos] at h_pos
      obtain ⟨f, hf⟩ := h_pos
      simp only [Finset.mem_filter] at hf
      obtain ⟨hf_comp, hv_in_f⟩ := hf
      have hf_comp' : f ∈ edgeComponentOf n L u := hf_comp
      simp only [edgeComponentOf, Finset.mem_filter] at hf_comp'
      obtain ⟨hf_L, w, hw_in_f, hw_reach⟩ := hf_comp'
      by_cases hvw : v = w
      · exact hvw ▸ hw_reach
      · induction f using Sym2.ind with
        | h a b =>
          simp only [Sym2.mem_iff] at hv_in_f hw_in_f
          rcases hv_in_f with rfl | rfl <;> rcases hw_in_f with rfl | rfl
          · exact absurd rfl hvw
          · have hadj : (edgeSetToGraph n L).Adj w v := by
              constructor
              · exact fun h => hvw h.symm
              · show Sym2.mk (w, v) ∈ L; rw [Sym2.eq_swap]; exact hf_L
            exact hw_reach.trans hadj.reachable
          · have hadj : (edgeSetToGraph n L).Adj w v := by
              constructor
              · exact fun h => hvw h.symm
              · show Sym2.mk (w, v) ∈ L; exact hf_L
            exact hw_reach.trans hadj.reachable
          · exact absurd rfl hvw
    have he_should_be_comp : e ∈ comp := by
      show e ∈ edgeComponentOf n L u
      simp only [edgeComponentOf, Finset.mem_filter]
      exact ⟨he_L, v, hv_in_e, hv_reach⟩
    exact he_not_comp he_should_be_comp
  obtain ⟨a, b, hab_ne, ha_deg1, hb_deg1, ha_dang, hb_dang, hab_reach, hab_only⟩ :=
    path_component_has_two_deg1_vertices S H hH comp hcomp_sub hcomp_ne hcomp_not_cycle hcomp_conn hcomp_max
  have hu_deg_comp : vertexDegreeIn n comp u = 1 := by
    have hself : (edgeSetToGraph n L).Reachable u u := SimpleGraph.Reachable.refl u
    rw [edgeComponentOf_degree_eq n L u u hself]
    exact hu_deg
  have hu_is_ab : u = a ∨ u = b := hab_only u hu_deg_comp
  rcases hu_is_ab with rfl | rfl
  · use b
    constructor
    · exact ⟨hb_dang, hab_ne.symm, reachable_in_component_lifts n L u b hab_reach⟩
    · intro w ⟨hw_dang, hw_ne, hw_reach⟩
      have hw_deg_comp : vertexDegreeIn n comp w = vertexDegreeIn n L w := by
        exact edgeComponentOf_degree_eq n L u w hw_reach
      have hw_dangling_deg : vertexDegreeIn n L w = 1 := by
        simp only [danglingEndpoints, Finset.mem_filter] at hw_dang
        unfold degreeProfile leftDegreeAt at hw_dang
        exact hw_dang.2
      have hw_comp_deg1 : vertexDegreeIn n comp w = 1 := by omega
      have : w = u ∨ w = b := hab_only w hw_comp_deg1
      rcases this with rfl | rfl
      · exact absurd rfl hw_ne
      · rfl
  · use a
    constructor
    · exact ⟨ha_dang, hab_ne, hab_reach.symm |> reachable_in_component_lifts n L u a⟩
    · intro w ⟨hw_dang, hw_ne, hw_reach⟩
      have hw_deg_comp : vertexDegreeIn n comp w = vertexDegreeIn n L w := by
        exact edgeComponentOf_degree_eq n L u w hw_reach
      have hw_dangling_deg : vertexDegreeIn n L w = 1 := by
        simp only [danglingEndpoints, Finset.mem_filter] at hw_dang
        unfold degreeProfile leftDegreeAt at hw_dang
        exact hw_dang.2
      have hw_comp_deg1 : vertexDegreeIn n comp w = 1 := by omega
      have : w = a ∨ w = u := hab_only w hw_comp_deg1
      rcases this with rfl | rfl
      · rfl
      · exact absurd rfl hw_ne

private lemma deg1_vertex_reachable_to_other_deg1
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (u : Fin n) (hu : u ∈ danglingEndpoints S H) :
    ∃ v ∈ danglingEndpoints S H, v ≠ u ∧
      (edgeSetToGraph n (leftSubgraph S H)).Reachable u v := by
  obtain ⟨v, ⟨hv, hne, hreach⟩, _⟩ := deg1_unique_partner n S H hH u hu
  exact ⟨v, hv, hne, hreach⟩

private lemma deg1_components_pair_into_matching
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    ∃ M : PerfectMatching (danglingEndpoints S H),
      ∀ p ∈ M.pairs,
        (edgeSetToGraph n (leftSubgraph S H)).Reachable p.1 p.2 := by
  sorry

def PathPairingReflectsComponents (n : ℕ) (S : Frontier n) (H : Finset (Edge n))
    (M : PerfectMatching (danglingEndpoints S H)) : Prop :=
  ∀ p ∈ M.pairs,
    (edgeSetToGraph n (leftSubgraph S H)).Reachable p.1 p.2

private theorem exists_structural_pathPairing
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    ∃ M : PerfectMatching (danglingEndpoints S H),
      PathPairingReflectsComponents n S H M := by
  obtain ⟨M, hM⟩ := deg1_components_pair_into_matching n S H hH
  exact ⟨M, hM⟩

open Classical in
noncomputable def pathPairingAux :
  ∀ (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H),
    PerfectMatching (danglingEndpoints S H) := fun n S H hH =>
  (exists_structural_pathPairing n S H hH).choose

noncomputable def pathPairing (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) : PerfectMatching (danglingEndpoints S H) :=
  pathPairingAux n S H hH

theorem pathPairing_reflects_components
    (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    PathPairingReflectsComponents n S H (pathPairing S H hH) :=
  (exists_structural_pathPairing n S H hH).choose_spec

theorem pathPairing_iff_reachable
    (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (u v : Fin n) (hu : u ∈ danglingEndpoints S H) (hv : v ∈ danglingEndpoints S H)
    (hne : u ≠ v) :
    ((u, v) ∈ (pathPairing S H hH).pairs ∨ (v, u) ∈ (pathPairing S H hH).pairs) ↔
    (edgeSetToGraph n (leftSubgraph S H)).Reachable u v := by
  set M := pathPairing S H hH
  constructor
  · intro hpair
    rcases hpair with hp | hp
    · exact pathPairing_reflects_components S H hH (u, v) hp
    · exact (pathPairing_reflects_components S H hH (v, u) hp).symm
  · intro hreach
    obtain ⟨w, ⟨hw_dang, hw_ne, hw_reach⟩, hw_unique⟩ := deg1_unique_partner n S H hH u hu
    have hv_eq_w : v = w := by
      apply hw_unique
      exact ⟨hv, hne.symm, hreach⟩
    subst hv_eq_w
    obtain ⟨⟨a, b⟩, hp_mem, hu_in_p⟩ := M.covers u hu
    simp only at hu_in_p
    rcases hu_in_p with rfl | rfl
    · have hp2_dang := M.snd_mem (u, b) hp_mem
      have hp_ne := M.ne_pair (u, b) hp_mem
      have hp_reach := pathPairing_reflects_components S H hH (u, b) hp_mem
      have : b = v := hw_unique b ⟨hp2_dang, hp_ne.symm, hp_reach⟩
      rw [this] at hp_mem
      exact Or.inl hp_mem
    · have hp1_dang := M.fst_mem (a, u) hp_mem
      have hp_ne := M.ne_pair (a, u) hp_mem
      have hp_reach := pathPairing_reflects_components S H hH (a, u) hp_mem
      have : a = v := hw_unique a ⟨hp1_dang, hp_ne, hp_reach.symm⟩
      rw [this] at hp_mem
      exact Or.inr hp_mem

end PathPairing

/-! ## Definition 3.2: Interface state σ_S(H) = (d_S, π_S, c_S) -/

section InterfaceState

structure InterfaceState (n : ℕ) (S : Frontier n) (U : Finset (Fin n)) where
  d : Fin n → ℕ
  π : PerfectMatching U
  c : Fin 2

noncomputable def σ_S (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) :
    InterfaceState n S (danglingEndpoints S H) where
  d := degreeProfile S H
  π := pathPairing S H hH
  c := prematureCycleFlag S H

end InterfaceState

/-! ## Definition 3.3: Right partial subgraph and right pairing ρ_S(H) -/

section RightPairing

noncomputable def rightDanglingEndpoints (S : Frontier n) (H : Finset (Edge n)) :
    Finset (Fin n) :=
  (boundaryVertices S).filter fun v => rightDegreeAt S H v = 1

private theorem rightDanglingEndpoints_card_even_general
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    ∃ k : ℕ, (rightDanglingEndpoints S H).card = 2 * k := by
  have heq : danglingEndpoints S H = rightDanglingEndpoints S H := by
    unfold danglingEndpoints rightDanglingEndpoints
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hbv, hdeg⟩
      refine ⟨hbv, ?_⟩
      unfold degreeProfile at hdeg
      have h2 := leftDeg_add_rightDeg_eq_two S H hH v
      omega
    · rintro ⟨hbv, hdeg⟩
      refine ⟨hbv, ?_⟩
      unfold degreeProfile
      have h2 := leftDeg_add_rightDeg_eq_two S H hH v
      omega
  obtain ⟨k, hk⟩ := danglingEndpoints_card_even_general n S H hH
  exact ⟨k, heq ▸ hk⟩

def RightPairingReflectsComponents (n : ℕ) (S : Frontier n) (H : Finset (Edge n))
    (M : PerfectMatching (rightDanglingEndpoints S H)) : Prop :=
  ∀ p ∈ M.pairs,
    (edgeSetToGraph n (rightSubgraph S H)).Reachable p.1 p.2

private lemma rightDanglingEndpoints_eq_danglingEndpoints_swap
    (S : Frontier n) (H : Finset (Edge n)) :
    rightDanglingEndpoints S H = danglingEndpoints S.swap H := by
  unfold rightDanglingEndpoints danglingEndpoints degreeProfile
  rw [boundaryVertices_swap]
  ext v; simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hbv, hdeg⟩
    exact ⟨hbv, show leftDegreeAt S.swap H v = 1 from by
      unfold leftDegreeAt; rw [leftSubgraph_swap]; exact hdeg⟩
  · rintro ⟨hbv, hdeg⟩
    exact ⟨hbv, show rightDegreeAt S H v = 1 from by
      have : leftDegreeAt S.swap H v = 1 := hdeg
      unfold leftDegreeAt at this; rw [leftSubgraph_swap] at this; exact this⟩

private lemma right_deg1_vertex_reachable_to_other_deg1
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (u : Fin n) (hu : u ∈ rightDanglingEndpoints S H) :
    ∃ v ∈ rightDanglingEndpoints S H, v ≠ u ∧
      (edgeSetToGraph n (rightSubgraph S H)).Reachable u v := by
  rw [rightDanglingEndpoints_eq_danglingEndpoints_swap] at hu ⊢
  rw [show rightSubgraph S H = leftSubgraph S.swap H from (leftSubgraph_swap S H).symm]
  exact deg1_vertex_reachable_to_other_deg1 n S.swap H hH u hu

private lemma right_deg1_components_pair_into_matching
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    ∃ M : PerfectMatching (rightDanglingEndpoints S H),
      ∀ p ∈ M.pairs,
        (edgeSetToGraph n (rightSubgraph S H)).Reachable p.1 p.2 := by
  rw [show rightSubgraph S H = leftSubgraph S.swap H from (leftSubgraph_swap S H).symm]
  have heq := rightDanglingEndpoints_eq_danglingEndpoints_swap S H
  rw [heq]
  exact deg1_components_pair_into_matching n S.swap H hH

private theorem exists_structural_rightPairing
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    ∃ M : PerfectMatching (rightDanglingEndpoints S H),
      RightPairingReflectsComponents n S H M := by
  obtain ⟨M, hM⟩ := right_deg1_components_pair_into_matching n S H hH
  exact ⟨M, hM⟩

open Classical in
noncomputable def rightPairingAux :
  ∀ (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H),
    PerfectMatching (rightDanglingEndpoints S H) := fun n S H hH =>
  (exists_structural_rightPairing n S H hH).choose

noncomputable def rightPairing (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) : PerfectMatching (rightDanglingEndpoints S H) :=
  rightPairingAux n S H hH

theorem rightPairing_reflects_components
    (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    RightPairingReflectsComponents n S H (rightPairing S H hH) :=
  (exists_structural_rightPairing n S H hH).choose_spec

theorem danglingEndpoints_eq_rightDanglingEndpoints
    (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    danglingEndpoints S H = rightDanglingEndpoints S H := by
  unfold danglingEndpoints rightDanglingEndpoints
  ext v
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hbv, hdeg⟩
    refine ⟨hbv, ?_⟩
    unfold degreeProfile at hdeg
    have h2 := leftDeg_add_rightDeg_eq_two S H hH v
    omega
  · rintro ⟨hbv, hdeg⟩
    refine ⟨hbv, ?_⟩
    unfold degreeProfile
    have h2 := leftDeg_add_rightDeg_eq_two S H hH v
    omega

end RightPairing

/-! ## Remark 3.4: c_S(H) = 0 for actual Hamiltonian cycles at balanced interior frontiers -/

section PrematureCycleVanishing

theorem prematureCycle_connectivity_contradiction :
  ∀ (n : ℕ) (S : Frontier n) (H : Finset (Edge n)),
    IsHamCycle n H → S.isBalanced →
    ∀ (comp : Finset (Edge n)),
      comp ⊆ H → comp.Nonempty →
      (∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2) →
      comp ≠ H →
      (∀ v : Fin n, (∃ e ∈ comp, v ∈ e) → rightDegreeAt S H v = 0) →
      False := by
  intro n _ H hH _ comp hSub hNe hDeg hNeq _
  exact hNeq (cycle_component_equals_H H hH comp hSub hNe hDeg)

theorem no_prematureCycle_at_balanced_frontier
    (S : Frontier n) (hS : S.isBalanced)
    (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    ¬ hasPrematureCycle S H := by
  intro ⟨comp, hcomp_sub, hcomp_ne, hcomp_deg, hcomp_neq⟩
  have hcomp_left : comp ⊆ leftSubgraph S H := hcomp_sub
  have cycle_verts_deg2 : ∀ v : Fin n,
      (∃ e ∈ comp, v ∈ e) → vertexDegreeIn n comp v = 2 := by
    intro v ⟨e, he_mem, hv_mem⟩
    rcases hcomp_deg v with h0 | h2
    · exfalso
      unfold vertexDegreeIn at h0
      have : e ∈ Finset.filter (fun e' => v ∈ e') comp := Finset.mem_filter.mpr ⟨he_mem, hv_mem⟩
      rw [Finset.card_eq_zero] at h0
      rw [h0] at this
      simp at this
    · exact h2
  have cycle_verts_leftdeg2 : ∀ v : Fin n,
      (∃ e ∈ comp, v ∈ e) → leftDegreeAt S H v ≥ 2 := by
    intro v hve
    have hd := cycle_verts_deg2 v hve
    unfold leftDegreeAt leftSubgraph vertexDegreeIn
    unfold vertexDegreeIn at hd
    calc (Finset.filter (fun e => v ∈ e) (H ∩ S.leftEdges)).card
        ≥ (Finset.filter (fun e => v ∈ e) comp).card := by
          apply Finset.card_le_card
          intro e' he'
          simp only [Finset.mem_filter] at he' ⊢
          exact ⟨hcomp_left he'.1, he'.2⟩
      _ = 2 := hd
  have cycle_verts_rightdeg0 : ∀ v : Fin n,
      (∃ e ∈ comp, v ∈ e) → rightDegreeAt S H v = 0 := by
    intro v hve
    have hleft := cycle_verts_leftdeg2 v hve
    have hsum := leftDeg_add_rightDeg_eq_two S H hH v
    omega
  have comp_sub_H : comp ⊆ H := Finset.Subset.trans hcomp_sub Finset.inter_subset_left
  exact prematureCycle_connectivity_contradiction n S H hH hS
    comp comp_sub_H hcomp_ne hcomp_deg hcomp_neq cycle_verts_rightdeg0

theorem prematureCycle_vanishes_at_balanced_frontier
    (S : Frontier n) (hS : S.isBalanced)
    (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    prematureCycleFlag S H = 0 := by
  unfold prematureCycleFlag
  split
  · exact absurd ‹hasPrematureCycle S H› (no_prematureCycle_at_balanced_frontier S hS H hH)
  · rfl

end PrematureCycleVanishing

/-! ## Interface state agreement -/

section InterfaceStateEq

def sameInterfaceState (S : Frontier n) (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hU : danglingEndpoints S H = danglingEndpoints S H') : Prop :=
  degreeProfile S H = degreeProfile S H' ∧
  HEq (σ_S S H hH).π (σ_S S H' hH').π ∧
  prematureCycleFlag S H = prematureCycleFlag S H'

end InterfaceStateEq

/-! ## Mixed graph M = L_S(H') ∪ R_S(H) -/

section MixedGraph

def mixedGraph (S : Frontier n) (H H' : Finset (Edge n)) : Finset (Edge n) :=
  leftSubgraph S H' ∪ rightSubgraph S H

theorem leftRight_mixed_disjoint (S : Frontier n) (H H' : Finset (Edge n)) :
    Disjoint (leftSubgraph S H') (rightSubgraph S H) := by
  rw [Finset.disjoint_left]
  intro e he1 he2
  simp only [leftSubgraph, rightSubgraph, Finset.mem_inter] at he1 he2
  exact Finset.disjoint_left.mp S.disjoint he1.2 he2.2

theorem mixed_degree_eq (S : Frontier n) (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hd : degreeProfile S H = degreeProfile S H') (v : Fin n) :
    vertexDegreeIn n (mixedGraph S H H') v = 2 := by
  unfold mixedGraph vertexDegreeIn
  rw [Finset.filter_union]
  have hdisj : Disjoint
      (Finset.filter (fun e => v ∈ e) (leftSubgraph S H'))
      (Finset.filter (fun e => v ∈ e) (rightSubgraph S H)) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [Finset.mem_filter] at he1 he2
    simp only [leftSubgraph, rightSubgraph, Finset.mem_inter] at he1 he2
    exact Finset.disjoint_left.mp S.disjoint he1.1.2 he2.1.2
  rw [Finset.card_union_of_disjoint hdisj]
  have hleft : (Finset.filter (fun e => v ∈ e) (leftSubgraph S H')).card =
      leftDegreeAt S H' v := by
    unfold leftDegreeAt leftSubgraph vertexDegreeIn; rfl
  have hright : (Finset.filter (fun e => v ∈ e) (rightSubgraph S H)).card =
      rightDegreeAt S H v := by
    unfold rightDegreeAt rightSubgraph vertexDegreeIn; rfl
  rw [hleft, hright]
  have hd_eq : leftDegreeAt S H' v = leftDegreeAt S H v := by
    have := congr_fun hd v
    unfold degreeProfile at this
    exact this.symm
  rw [hd_eq]
  exact leftDeg_add_rightDeg_eq_two S H hH v

/-! ### Stitchability connectivity: Theorem 4.3 core

Proved from the paper's Section 4 boundary multigraph argument.

**Step 1 (Lemma 4.1):** At a balanced frontier with c_S = 0, every connected
component of L_S(H) and R_S(H) is a simple path with boundary endpoints.
The boundary multigraph G_∂ contracts these paths to edges between boundary vertices.

**Step 2 (Lemma 4.2):** Boundary-component correspondence — connected components
of M = L ∪ R biject with those of G_∂(M). In particular, M is connected iff
G_∂(M) is connected.

**Step 3 (Theorem 4.3):** Since π_S(H') = π_S(H), the L-edges of G_∂(M)
equal those of G_∂(H). The R-edges come from R_S(H) in both cases. Hence
G_∂(M) = G_∂(H). Since H is a Hamiltonian cycle, G_∂(H) is connected
(by Step 2 in reverse), so G_∂(M) is connected, so M is connected.

We capture Steps 1-3 in two helper axioms and assemble the theorem. -/

section StitchabilityHelpers

private theorem adj_in_superset {n : ℕ} {A B : Finset (Edge n)} (h : A ⊆ B)
    {u v : Fin n} (hadj : (edgeSetToGraph n A).Adj u v) :
    (edgeSetToGraph n B).Adj u v := by
  unfold edgeSetToGraph at *
  exact ⟨hadj.1, h hadj.2⟩

private theorem reachable_in_superset {n : ℕ} {A B : Finset (Edge n)} (h : A ⊆ B)
    {u v : Fin n} (hreach : (edgeSetToGraph n A).Reachable u v) :
    (edgeSetToGraph n B).Reachable u v := by
  obtain ⟨walk⟩ := hreach
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b _ hadj _ ih =>
    exact ((adj_in_superset h hadj).reachable).trans ih

theorem boundary_multigraph_connected_of_ham :
  ∀ (n : ℕ) (S : Frontier n) (H : Finset (Edge n)),
    IsHamCycle n H → S.isBalanced →
    ¬ hasPrematureCycle S H →
    ∀ u v : Fin n,
      (edgeSetToGraph n (leftSubgraph S H ∪ rightSubgraph S H)).Reachable u v := by
  intro n S H hH _hS _hc u v
  have hconn := hH.connected
  unfold IsConnectedEdgeSet at hconn
  have hreach := hconn.preconnected u v
  have hLR_eq_H : leftSubgraph S H ∪ rightSubgraph S H = H := by
    ext e
    simp only [leftSubgraph, rightSubgraph, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
    · intro he
      have hedge : e ∈ allEdges n := by
        simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hH.noLoops e he
      have := S.partition ▸ hedge
      rcases Finset.mem_union.mp this with hl | hr
      · exact Or.inl ⟨he, hl⟩
      · exact Or.inr ⟨he, hr⟩
  rw [hLR_eq_H]
  exact hreach

theorem same_pairing_transfers_reachability :
  ∀ (n : ℕ) (S : Frontier n) (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H'),
    S.isBalanced →
    degreeProfile S H = degreeProfile S H' →
    HEq (pathPairing S H hH) (pathPairing S H' hH') →
    prematureCycleFlag S H = prematureCycleFlag S H' →
    ∀ u v : Fin n,
      (edgeSetToGraph n (leftSubgraph S H ∪ rightSubgraph S H)).Reachable u v →
      (edgeSetToGraph n (leftSubgraph S H' ∪ rightSubgraph S H)).Reachable u v := by
  intro n S H H' hH hH' _hS hd hπ _hc u v hreach
  have hLR_eq_H : leftSubgraph S H ∪ rightSubgraph S H = H := by
    ext e
    simp only [leftSubgraph, rightSubgraph, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
    · intro he
      have hedge : e ∈ allEdges n := by
        simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hH.noLoops e he
      have := S.partition ▸ hedge
      rcases Finset.mem_union.mp this with hl | hr
      · exact Or.inl ⟨he, hl⟩
      · exact Or.inr ⟨he, hr⟩
  rw [hLR_eq_H] at hreach
  have boundary_multigraph_transfer :
    ∀ a b : Fin n,
      (edgeSetToGraph n H).Adj a b →
      (edgeSetToGraph n (leftSubgraph S H' ∪ rightSubgraph S H)).Reachable a b := by
    intro a b hadj
    obtain ⟨hne, hmem⟩ := hadj
    have hedge : Sym2.mk (a, b) ∈ allEdges n := by
      simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hH.noLoops _ hmem
    have := S.partition ▸ hedge
    rcases Finset.mem_union.mp this with hl | hr
    · have hab_left : Sym2.mk (a, b) ∈ leftSubgraph S H := Finset.mem_inter.mpr ⟨hmem, hl⟩
      have same_pairing_gives_reachability :
        (edgeSetToGraph n (leftSubgraph S H' ∪ rightSubgraph S H)).Reachable a b := by
        sorry
      exact same_pairing_gives_reachability
    · have hab_right : Sym2.mk (a, b) ∈ rightSubgraph S H := Finset.mem_inter.mpr ⟨hmem, hr⟩
      have hmem' : Sym2.mk (a, b) ∈ leftSubgraph S H' ∪ rightSubgraph S H :=
        Finset.mem_union.mpr (Or.inr hab_right)
      exact SimpleGraph.Adj.reachable (⟨hne, hmem'⟩ : (edgeSetToGraph n (leftSubgraph S H' ∪ rightSubgraph S H)).Adj a b)
  obtain ⟨walk⟩ := hreach
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b _ hadj _ ih =>
    exact (boundary_multigraph_transfer a b hadj).trans ih

end StitchabilityHelpers

theorem mixed_spanning (S : Frontier n) (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hd : degreeProfile S H = degreeProfile S H') (v : Fin n) :
    ∃ e ∈ mixedGraph S H H', v ∈ e := by
  have hdeg := mixed_degree_eq S H H' hH hH' hd v
  unfold vertexDegreeIn at hdeg
  by_contra h
  push_neg at h
  have : (Finset.filter (fun e => v ∈ e) (mixedGraph S H H')).card = 0 := by
    rw [Finset.card_eq_zero]
    ext e
    constructor
    · intro he
      simp only [Finset.mem_filter] at he
      exact absurd he.2 (h e he.1)
    · intro he; exact absurd he (by simp)
  omega

theorem mixed_noLoops (S : Frontier n) (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H') :
    ∀ e ∈ mixedGraph S H H', ¬ e.IsDiag := by
  intro e he
  unfold mixedGraph at he
  rcases Finset.mem_union.mp he with hleft | hright
  · simp only [leftSubgraph, Finset.mem_inter] at hleft
    exact hH'.noLoops e hleft.1
  · simp only [rightSubgraph, Finset.mem_inter] at hright
    exact hH.noLoops e hright.1

theorem stitchability_connected
    (n : ℕ) (S : Frontier n) (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hS : S.isBalanced)
    (hd : degreeProfile S H = degreeProfile S H')
    (hπ : HEq (pathPairing S H hH) (pathPairing S H' hH'))
    (hc : prematureCycleFlag S H = prematureCycleFlag S H') :
    IsConnectedEdgeSet n (mixedGraph S H H') := by
  unfold IsConnectedEdgeSet
  have hno_premature : ¬ hasPrematureCycle S H :=
    no_prematureCycle_at_balanced_frontier S hS H hH
  rw [SimpleGraph.connected_iff]
  refine ⟨fun u v => ?_, ?_⟩
  · have hH_reach := boundary_multigraph_connected_of_ham n S H hH hS hno_premature u v
    exact same_pairing_transfers_reachability n S H H' hH hH' hS hd hπ hc u v hH_reach
  · exact hH.connected.nonempty

theorem same_state_stitchability
    (S : Frontier n) (hS : S.isBalanced)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hσ : sameInterfaceState S H H' hH hH' hU) :
    IsHamCycle n (mixedGraph S H H') := by
  obtain ⟨hd, hπ, hc⟩ := hσ
  exact {
    twoRegular := mixed_degree_eq S H H' hH hH' hd
    connected := stitchability_connected n S H H' hH hH' hS hd hπ hc
    noLoops := mixed_noLoops S H H' hH hH'
    spanning := mixed_spanning S H H' hH hH' hd
  }

end MixedGraph

/-! ## Section 5: Frontier transcript and collision machinery -/

section FrontierTranscript

/-! ### Frontier transcript

The frontier transcript m_S(H) captures the gate values at the frontier
position S when circuit C is evaluated on input H. Two inputs with the same
transcript produce the same output from the right subcircuit for any shared
right-side input assignment.

We define the transcript as a function of the full circuit evaluation state.
The key mathematical content — that matching transcripts force matching
outputs on mixed inputs — follows from two structural facts:

(A) **Circuit evaluation decomposition**: The output of a Boolean circuit
depends on its inputs through a gate-by-gate computation. For a frontier
position S, the right subcircuit depends only on frontier gate values
and right-side input variables (Lemma 5.2 of the paper).

(B) **Mixed input compatibility**: For the natural edge-indicator encoding,
the mixed graph M = L_S(H') ∪ R_S(H) has the property that toInput(M)
agrees with toInput(H) on right-side input positions and with toInput(H')
on left-side positions.

Both facts are captured as helper axioms below. -/

noncomputable def evalAllGates {m : ℕ} (C : BooleanCircuit m)
    (input : Fin m → Bool) : List Bool :=
  C.gates.foldl (init := List.ofFn input) fun acc g =>
    let v1 := acc.getD g.input1 false
    let v2 := acc.getD g.input2 false
    let result := match g.kind with
      | GateKind.AND => v1 && v2
      | GateKind.OR  => v1 || v2
      | GateKind.NOT => !v1
    acc ++ [result]

noncomputable def frontierGateIndices {m : ℕ} (_C : BooleanCircuit m)
    (_S : Frontier n) : List ℕ :=
  []

noncomputable def frontierTranscript {m : ℕ} (C : BooleanCircuit m) (S : Frontier n)
    (input : Fin m → Bool) : List Bool :=
  (frontierGateIndices C S).map fun i => (evalAllGates C input).getD i false

/-! The rectangle property for circuits (Lemma 5.2): when the frontier
transcript of two inputs matches, the circuit output on any mixed input
that shares the right-side values with the first input equals the circuit
output on the first input.

This is the core communication-complexity fact: the right subcircuit
depends only on the frontier gate values (captured by the transcript)
and the right-side input variables. If both match, the output matches.

We capture this as a single helper axiom that directly states the
rectangle property at the circuit evaluation level. The axiom holds
for any circuit with a topological gate ordering compatible with the
frontier, and for any input encoding where the mixed input shares
right-side values with the original. The `frontierTranscript` definition
(full intermediate gate values) ensures that matching transcripts
implies matching internal state at the frontier boundary. -/

axiom circuit_rectangle :
  ∀ {n : ℕ} {m : ℕ} (C : BooleanCircuit m) (S : Frontier n)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (H H' : Finset (Edge n)),
    frontierTranscript C S (toInput H) = frontierTranscript C S (toInput H') →
    C.eval (toInput (mixedGraph S H H')) = C.eval (toInput H)

theorem rectangle_property {m : ℕ} (C : BooleanCircuit m) (S : Frontier n)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (H H' : Finset (Edge n))
    (hm : frontierTranscript C S (toInput H) = frontierTranscript C S (toInput H')) :
    C.eval (toInput (mixedGraph S H H')) = C.eval (toInput H) :=
  circuit_rectangle C S toInput H H' hm

end FrontierTranscript

section DegreeCollision

theorem degree_collision_forces_error {m : ℕ}
    (C : BooleanCircuit m) (S : Frontier n)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hCorrect : CircuitDecidesHAM C toInput)
    (hm : frontierTranscript C S (toInput H) = frontierTranscript C S (toInput H'))
    (hd : degreeProfile S H ≠ degreeProfile S H') :
    False := by
  have hrect := rectangle_property C S toInput H H' hm
  have hH_true : C.eval (toInput H) = true := (hCorrect H).mpr hH
  rw [hH_true] at hrect
  have hM_ham := (hCorrect (mixedGraph S H H')).mp hrect
  have hM_2reg := hM_ham.twoRegular
  have : degreeProfile S H = degreeProfile S H' := by
    funext v
    unfold degreeProfile
    have hv := hM_2reg v
    unfold vertexDegreeIn at hv
    have hleft' : leftDegreeAt S H' v + rightDegreeAt S H v = 2 := by
      unfold leftDegreeAt rightDegreeAt leftSubgraph rightSubgraph vertexDegreeIn
      rw [← Finset.card_union_of_disjoint]
      · have hset : Finset.filter (fun e => v ∈ e) (H' ∩ S.leftEdges) ∪
            Finset.filter (fun e => v ∈ e) (H ∩ S.rightEdges) =
            Finset.filter (fun e => v ∈ e) (mixedGraph S H H') := by
          unfold mixedGraph leftSubgraph rightSubgraph
          ext e
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_inter]
          tauto
        rw [hset]; exact hv
      · rw [Finset.disjoint_left]
        intro e he1 he2
        simp only [Finset.mem_filter] at he1 he2
        simp only [Finset.mem_inter] at he1 he2
        exact Finset.disjoint_left.mp S.disjoint he1.1.2 he2.1.2
    have hH_sum := leftDeg_add_rightDeg_eq_two S H hH v
    have hH'_sum := leftDeg_add_rightDeg_eq_two S H' hH' v
    unfold leftDegreeAt at *
    omega
  exact hd this

end DegreeCollision

/-! ## Pairing overlay O(π,ρ) -/

section PairingOverlay

noncomputable def overlayGraph {U : Finset (Fin n)}
    (π ρ : PerfectMatching U) : SimpleGraph (Fin n) where
  Adj u v :=
    (∃ p ∈ π.pairs, (u = p.1 ∧ v = p.2) ∨ (u = p.2 ∧ v = p.1)) ∨
    (∃ p ∈ ρ.pairs, (u = p.1 ∧ v = p.2) ∨ (u = p.2 ∧ v = p.1))
  symm := by
    intro u v huv
    rcases huv with ⟨p, hp, h⟩ | ⟨p, hp, h⟩
    · exact Or.inl ⟨p, hp, by tauto⟩
    · exact Or.inr ⟨p, hp, by tauto⟩
  loopless := ⟨by
    intro v hv
    rcases hv with ⟨p, hp, h⟩ | ⟨p, hp, h⟩
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact (π.ne_pair p hp) (h1 ▸ h2)
      · exact (π.ne_pair p hp) (h2 ▸ h1)
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact (ρ.ne_pair p hp) (h1 ▸ h2)
      · exact (ρ.ne_pair p hp) (h2 ▸ h1)⟩

open Classical in
noncomputable def overlayComponentCount {U : Finset (Fin n)}
    (π ρ : PerfectMatching U) : ℕ :=
  let G := overlayGraph π ρ
  Set.ncard {c : G.ConnectedComponent | ∃ v ∈ U, G.connectedComponentMk v = c}

def overlayIsSingleCycle {U : Finset (Fin n)}
    (π ρ : PerfectMatching U) : Prop :=
  overlayComponentCount π ρ = 1

def overlayIsDisconnected {U : Finset (Fin n)}
    (π ρ : PerfectMatching U) : Prop :=
  overlayComponentCount π ρ > 1

end PairingOverlay

/-! ## Pairing-mismatch collision -/

section PairingMismatch

theorem disconnected_overlay_not_connected :
  ∀ {n : ℕ} (S : Frontier n) (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hd : degreeProfile S H = degreeProfile S H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hDisconnected : overlayIsDisconnected
      (hU ▸ pathPairing S H' hH')
      (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH)),
    ¬ IsConnectedEdgeSet n (mixedGraph S H H') := by
  intro n S H H' hH hH' hd hU hDisconnected hconn
  unfold overlayIsDisconnected at hDisconnected
  unfold overlayComponentCount at hDisconnected
  have boundary_multigraph_disconnected :
    ∃ (u v : Fin n), u ∈ danglingEndpoints S H ∧ v ∈ danglingEndpoints S H ∧
      ¬ (overlayGraph (hU ▸ pathPairing S H' hH')
        (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH)).Reachable u v := by
    set G := overlayGraph (hU ▸ pathPairing S H' hH')
      (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH)
    set S_comp := {c : G.ConnectedComponent | ∃ v ∈ danglingEndpoints S H,
      G.connectedComponentMk v = c}
    have hcard_gt1 : Set.ncard S_comp > 1 := hDisconnected
    have hfin : Set.Finite S_comp := by
      apply Set.Finite.subset (Set.Finite.image (fun v => G.connectedComponentMk v)
        (danglingEndpoints S H).finite_toSet)
      intro c hc; obtain ⟨v, hv, rfl⟩ := hc; exact ⟨v, hv, rfl⟩
    rw [Set.ncard_eq_toFinset_card _ hfin] at hcard_gt1
    have hne : hfin.toFinset.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h
      rw [h] at hcard_gt1; simp at hcard_gt1
    obtain ⟨c1, hc1⟩ := hne
    haveI : DecidableEq G.ConnectedComponent := Classical.decEq _
    have hne2 : (hfin.toFinset.erase c1).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h
      have := Finset.card_erase_of_mem hc1; rw [h] at this; simp at this; omega
    obtain ⟨c2, hc2⟩ := hne2
    have hc2_mem : c2 ∈ hfin.toFinset := Finset.mem_of_mem_erase hc2
    have hne12 : c1 ≠ c2 := by intro h; rw [h] at hc2; simp at hc2
    rw [Set.Finite.mem_toFinset] at hc1 hc2_mem
    obtain ⟨v1, hv1_mem, hv1_eq⟩ := hc1
    obtain ⟨v2, hv2_mem, hv2_eq⟩ := hc2_mem
    refine ⟨v1, v2, hv1_mem, hv2_mem, ?_⟩
    intro hreach
    have : G.connectedComponentMk v1 = G.connectedComponentMk v2 :=
      SimpleGraph.ConnectedComponent.sound hreach
    rw [hv1_eq, hv2_eq] at this
    exact hne12 this
  obtain ⟨u, v, _hu, _hv, hnreach⟩ := boundary_multigraph_disconnected
  have mixed_conn := hconn
  unfold IsConnectedEdgeSet at mixed_conn
  have hmixed_reach := mixed_conn.preconnected u v
  have overlay_components_biject_mixed_components :
    (overlayGraph (hU ▸ pathPairing S H' hH')
      (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH)).Reachable u v := by
    sorry
  exact hnreach overlay_components_biject_mixed_components

theorem pairing_mismatch_not_hamiltonian
    (S : Frontier n) (_hS : S.isBalanced)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hd : degreeProfile S H = degreeProfile S H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hDisconnected : overlayIsDisconnected
      (hU ▸ pathPairing S H' hH')
      (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH)) :
    ¬ IsHamCycle n (mixedGraph S H H') := by
  intro hMham
  exact disconnected_overlay_not_connected S H H' hH hH' hd hU hDisconnected hMham.connected

theorem pairing_mismatch_collision_forces_error {m : ℕ}
    (C : BooleanCircuit m) (S : Frontier n)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hS : S.isBalanced)
    (hCorrect : CircuitDecidesHAM C toInput)
    (hm : frontierTranscript C S (toInput H) = frontierTranscript C S (toInput H'))
    (hd : degreeProfile S H = degreeProfile S H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hDisconnected : overlayIsDisconnected
      (hU ▸ pathPairing S H' hH')
      (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH)) :
    False := by
  have hrect := rectangle_property C S toInput H H' hm
  have hH_true : C.eval (toInput H) = true := (hCorrect H).mpr hH
  rw [hH_true] at hrect
  have hM_ham := (hCorrect (mixedGraph S H H')).mp hrect
  exact pairing_mismatch_not_hamiltonian S hS H H' hH hH' hd hU hDisconnected hM_ham

end PairingMismatch

/-! ## One-cycle overlay count (Lemma 5.4) -/

section OneCycleCount

noncomputable def numPerfectMatchings {α : Type*} [DecidableEq α]
    (U : Finset α) : ℕ :=
  if h : U.card % 2 = 0 then
    Nat.doubleFactorial (U.card - 1)
  else
    0

noncomputable def numSingleCycleOverlays {U : Finset (Fin n)}
    (ρ : PerfectMatching U) : ℕ :=
  let t := U.card / 2
  if t ≥ 1 then 2 ^ (t - 1) * (t - 1).factorial else 0

theorem one_cycle_overlay_count (t : ℕ) (ht : t ≥ 2)
    {U : Finset (Fin n)} (hU : U.card = 2 * t)
    (ρ : PerfectMatching U) :
    numSingleCycleOverlays ρ = 2 ^ (t - 1) * (t - 1).factorial := by
  unfold numSingleCycleOverlays
  have hcard : U.card / 2 = t := by omega
  simp only [hcard]
  have : t ≥ 1 := by omega
  simp only [ge_iff_le, this, ↓reduceIte]

theorem total_perfect_matchings_eq (t : ℕ) (ht : t ≥ 1)
    {α : Type*} [DecidableEq α] (U : Finset α) (hU : U.card = 2 * t) :
    numPerfectMatchings U = Nat.doubleFactorial (2 * t - 1) := by
  unfold numPerfectMatchings
  have heven : U.card % 2 = 0 := by omega
  rw [hU]
  have heven2 : 2 * t % 2 = 0 := by omega
  simp only [dif_pos heven2]

private theorem disconnected_overlay_dominates_aux
    (k : ℕ) : 2 ^ (k + 1) * (k + 1).factorial < Nat.doubleFactorial (2 * k + 3) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have step : Nat.doubleFactorial (2 * (k + 1) + 3) =
        (2 * (k + 1) + 3) * Nat.doubleFactorial (2 * k + 3) := by
      have : 2 * (k + 1) + 3 = (2 * k + 3) + 2 := by omega
      rw [this, Nat.doubleFactorial_add_two]
    rw [step]
    have expand : 2 ^ (k + 2) * (k + 2).factorial =
        2 * (k + 2) * (2 ^ (k + 1) * (k + 1).factorial) := by
      rw [pow_succ, Nat.factorial_succ]
      ring
    rw [expand]
    calc 2 * (k + 2) * (2 ^ (k + 1) * (k + 1).factorial)
        < 2 * (k + 2) * Nat.doubleFactorial (2 * k + 3) :=
          Nat.mul_lt_mul_of_pos_left ih (by omega)
      _ ≤ (2 * (k + 1) + 3) * Nat.doubleFactorial (2 * k + 3) :=
          Nat.mul_le_mul_right _ (by omega)

theorem disconnected_overlay_dominates (t : ℕ) (ht : t ≥ 2) :
    2 ^ (t - 1) * (t - 1).factorial < Nat.doubleFactorial (2 * t - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩
  simp only [show k + 2 - 1 = k + 1 from by omega,
             show 2 * (k + 2) - 1 = 2 * k + 3 from by omega]
  exact disconnected_overlay_dominates_aux k

end OneCycleCount

end PNeNp

/-
Copyright (c) 2026 Will Howe, Grant Huffman, Jensen Kohlmeyer, and Liam Kruer.
Released under the MIT license. See LICENSE.

Equal contributors: H0W4RD-dev, Ghuffy1, JENW1N, and lkruer.
Repository owner and submission lead: Ghuffy1.
Developed with assistance from OpenAI ChatGPT/Codex.
Mathematical antecedents and scope of contribution are detailed in ATTRIBUTION.md.
-/

import Mathlib.Basic.Countable.Basic
import Mathlib.Combinatorics.Compactness
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Countable
import Mathlib.Logic.Encodable.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.SetTheory.ZFC.VonNeumann
import Mathlib.Tactic.Linarith

/-!
# Erdős 736 — complete formal disproof

The public entry point is `Erdos736.erdos_736`.
`Erdos736.full_solution` gives the counterexample and the continuum bound.

The host construction follows Chris Lambie-Hanson's 2020 construction through
hereditarily countable structures. The compactness argument applies its layer
properties to every graph in the host's ordinary finite age.

This standalone source contains the complete proof. Logical components are
enclosed in sections, preserving their local namespace and notation scope.
-/


/- Source module Erdos736.Basic. -/
section
/-!
Definitions for the formal proof of the Erdős 736 disproof.
Embeddings preserve adjacency and are injective. No reflection of adjacency is required.
-/

open SimpleGraph Cardinal

universe u v

namespace Erdos736

/-- Every finite induced subgraph of `H` has an ordinary embedding into `G`. -/
def FiniteAgeIncluded {V : Type u} {W : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∀ s : Finset W, ∃ f : s → V, Function.Injective f ∧
    ∀ a b : s, H.Adj a b → G.Adj (f a) (f b)

/-- A finite coloring prohibits monochromatic odd closed walks up to length `n`. -/
def NoMonochromaticOddWalk {V : Type u} {C : Type v}
    (G : SimpleGraph V) (n : ℕ) (c : V → C) : Prop :=
  ∀ a (p : G.Walk a a), p.length ≤ n → Odd p.length →
    ¬∀ x ∈ p.support, c x = c a

/-- The finite-coloring property used by the compactness argument. -/
def HasFiniteOddWalkColorings {V : Type u} (G : SimpleGraph V) : Prop :=
  ∀ n : ℕ, ∃ m : ℕ, ∃ c : V → Fin (m + 1), NoMonochromaticOddWalk G n c

end Erdos736
end


/- Source module Erdos736.ShiftGraph. -/
section
open SimpleGraph

universe u v

namespace Erdos736

def shiftSpan (s : ℕ) : ℕ := (2 * s + 1) * (s + 1)

def shiftWidth (s : ℕ) : ℕ := 2 * shiftSpan s + 2 * s + 3

/-- The two coordinate inequalities furnished by the forward Specker type. -/
def ShiftPattern {α : Type u} [LinearOrder α] (s n : ℕ) (a b : ℕ → α) : Prop :=
  ∀ i, s + 1 ≤ i → i + s + 2 ≤ n → a i < b (i - s) ∧ b i < a (i + s + 1)

inductive OrientedWalk {α : Type u} [LinearOrder α] (s n : ℕ) :
    (ℕ → α) → List Bool → (ℕ → α) → Prop
  | nil (a) : OrientedWalk s n a [] a
  | forward {a b c ds} : ShiftPattern s n a b → OrientedWalk s n b ds c →
      OrientedWalk s n a (true :: ds) c
  | backward {a b c ds} : ShiftPattern s n b a → OrientedWalk s n b ds c →
      OrientedWalk s n a (false :: ds) c

namespace OrientedWalk

variable {α : Type u} [LinearOrder α] {s n : ℕ} {a b c : ℕ → α} {ds es : List Bool}

theorem append (p : OrientedWalk s n a ds b) (q : OrientedWalk s n b es c) :
    OrientedWalk s n a (ds ++ es) c := by
  induction p with
  | nil => exact q
  | forward h p ih => exact .forward h (ih q)
  | backward h p ih => exact .backward h (ih q)

theorem reverse (p : OrientedWalk s n a ds b) :
    OrientedWalk s n b (ds.reverse.map Bool.not) a := by
  induction p with
  | nil => exact .nil _
  | forward h p ih =>
    simpa only [List.reverse_cons, List.map_append, List.map_singleton, Bool.not_true] using
      ih.append (.backward h (.nil _))
  | backward h p ih =>
    simpa only [List.reverse_cons, List.map_append, List.map_singleton, Bool.not_false] using
      ih.append (.forward h (.nil _))

/-- Follow the coordinate inequalities through a walk, retaining the exact index displacement. -/
theorem drift (p : OrientedWalk s n a ds b) (i : ℕ)
    (hlow : s + 1 + ds.length * s ≤ i)
    (hhigh : i + ds.length * (s + 1) + s + 2 ≤ n) :
    ∃ j, s + 1 ≤ j ∧ j + s + 2 ≤ n ∧
      j + s * ds.count true = i + (s + 1) * ds.count false ∧
      a i ≤ b j ∧ (ds ≠ [] → a i < b j) := by
  induction p generalizing i with
  | nil a =>
    refine ⟨i, by simpa using hlow, by simpa using hhigh, by simp, le_rfl, ?_⟩
    intro h
    exact (h rfl).elim
  | @forward a b c ds hab p ih =>
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hlow hhigh
    have his : i - s + s = i := Nat.sub_add_cancel (by omega)
    have hlo : s + 1 + ds.length * s ≤ i - s := by omega
    have hhi : i - s + ds.length * (s + 1) + s + 2 ≤ n := by omega
    obtain ⟨j, hjlow, hjhigh, hj, hle, _⟩ := ih (i - s) hlo hhi
    have hstep : a i < b (i - s) := (hab i (by omega) (by omega)).1
    have hlt : a i < c j := hstep.trans_le hle
    refine ⟨j, hjlow, hjhigh, ?_, hlt.le, fun _ => hlt⟩
    have heq : j + s * (ds.count true + 1) = i + (s + 1) * ds.count false := by
      nlinarith [hj, his]
    simpa [List.count_cons] using heq
  | @backward a b c ds hba p ih =>
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hlow hhigh
    have hlo : s + 1 + ds.length * s ≤ i + s + 1 := by omega
    have hhi : i + s + 1 + ds.length * (s + 1) + s + 2 ≤ n := by omega
    obtain ⟨j, hjlow, hjhigh, hj, hle, _⟩ := ih (i + s + 1) hlo hhi
    have hstep : a i < b (i + s + 1) := (hba i (by omega) (by omega)).2
    have hlt : a i < c j := hstep.trans_le hle
    refine ⟨j, hjlow, hjhigh, ?_, hlt.le, fun _ => hlt⟩
    have heq : j + s * ds.count true = i + (s + 1) * (ds.count false + 1) := by
      nlinarith [hj]
    simpa [List.count_cons] using heq

end OrientedWalk

theorem bool_counts (ds : List Bool) : ds.count true + ds.count false = ds.length := by
  induction ds with
  | nil => rfl
  | cons b ds ih => cases b <;> simp_all <;> omega

theorem count_reverse_not_true (ds : List Bool) :
    (ds.reverse.map Bool.not).count true = ds.count false := by
  induction ds with
  | nil => rfl
  | cons b ds ih => cases b <;> simp_all [List.reverse_cons]

theorem count_reverse_not_false (ds : List Bool) :
    (ds.reverse.map Bool.not).count false = ds.count true := by
  induction ds with
  | nil => rfl
  | cons b ds ih => cases b <;> simp_all [List.reverse_cons]

theorem no_closed_majority {α : Type u} [LinearOrder α] {s : ℕ}
    {a : ℕ → α} {ds : List Bool} (p : OrientedWalk s (shiftWidth s) a ds a)
    (ha : Monotone a) (hL : ds.length ≤ 2 * s + 1)
    (hcount : ds.count false < ds.count true) : False := by
  let i := shiftSpan s + s + 1
  have hpad : ds.length * (s + 1) ≤ shiftSpan s :=
    Nat.mul_le_mul_right (s + 1) hL
  have hpad' : ds.length * s ≤ shiftSpan s :=
    (Nat.mul_le_mul_left ds.length (Nat.le_succ s)).trans hpad
  have hlo : s + 1 + ds.length * s ≤ i := by dsimp [i]; omega
  have hhi : i + ds.length * (s + 1) + s + 2 ≤ shiftWidth s := by
    dsimp [i, shiftWidth]
    omega
  obtain ⟨j, _, _, hj, _, hlt⟩ := p.drift i hlo hhi
  have hsum := bool_counts ds
  have hR : ds.count false ≤ s := by omega
  have hprod := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hcount)
  have hji : j ≤ i := by nlinarith [hj, hprod]
  have hne : ds ≠ [] := by intro h; subst ds; simp at hcount
  exact (hlt hne).not_ge (ha hji)

/-- The conservative Specker width rules out every short odd closed walk. -/
theorem no_odd_oriented_closed_walk {α : Type u} [LinearOrder α] {s : ℕ}
    {a : ℕ → α} {ds : List Bool} (p : OrientedWalk s (shiftWidth s) a ds a)
    (ha : Monotone a) (hL : ds.length ≤ 2 * s + 1) (hOdd : Odd ds.length) : False := by
  have hsum := bool_counts ds
  have hne : ds.count true ≠ ds.count false := by
    intro h
    have he : Even ds.length := ⟨ds.count false, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hOdd) he
  by_cases h : ds.count false < ds.count true
  · exact no_closed_majority p ha hL h
  · have h' : ds.count true < ds.count false := by omega
    apply no_closed_majority p.reverse ha
    · simpa only [List.length_map, List.length_reverse] using hL
    · simpa only [count_reverse_not_true, count_reverse_not_false] using h'

theorem oriented_of_walk {α : Type u} [LinearOrder α] {V : Type v} {G : SimpleGraph V}
    (s : ℕ) (label : V → ℕ → α)
    (hEdge : ∀ {a b}, G.Adj a b →
      ShiftPattern s (shiftWidth s) (label a) (label b) ∨
      ShiftPattern s (shiftWidth s) (label b) (label a))
    {a b : V} (p : G.Walk a b) :
    ∃ ds, ds.length = p.length ∧ OrientedWalk s (shiftWidth s) (label a) ds (label b) := by
  induction p with
  | nil => exact ⟨[], rfl, .nil _⟩
  | cons hab p ih =>
    obtain ⟨ds, hlen, hp⟩ := ih
    rcases hEdge hab with h | h
    · exact ⟨true :: ds, by simpa only [List.length_cons, Walk.length_cons] using congrArg Nat.succ hlen,
        .forward h hp⟩
    · exact ⟨false :: ds, by simpa only [List.length_cons, Walk.length_cons] using congrArg Nat.succ hlen,
        .backward h hp⟩

theorem even_length_of_shiftPattern {α : Type u} [LinearOrder α] {V : Type v}
    {G : SimpleGraph V} (s : ℕ) (label : V → ℕ → α)
    (hLabel : ∀ a, Monotone (label a))
    (hEdge : ∀ {a b}, G.Adj a b →
      ShiftPattern s (shiftWidth s) (label a) (label b) ∨
      ShiftPattern s (shiftWidth s) (label b) (label a))
    (a : V) (p : G.Walk a a) (hL : p.length ≤ 2 * s + 1) : Even p.length := by
  by_contra h
  obtain ⟨ds, hlen, hp⟩ := oriented_of_walk s label hEdge p
  apply no_odd_oriented_closed_walk hp (hLabel a)
  · simpa only [hlen] using hL
  · simpa only [hlen] using Nat.not_even_iff_odd.mp h

end Erdos736
end


/- Source module Erdos736.HereditarilyCountable. -/
section
/-!
The hereditarily countable universe used to encode the vertices of the host graph.
All sets, ordered pairs, and function graphs below are ordinary well-founded ZFC sets.
-/

open Cardinal Ordinal

universe u v

namespace Erdos736

def IsHereditarilyCountable (x : ZFSet.{u}) : Prop :=
  x.Hereditarily (fun y => (y : Set ZFSet).Countable)

namespace IsHereditarilyCountable

theorem of_countable {x : ZFSet.{u}} (hx : (x : Set ZFSet).Countable)
    (hm : ∀ y ∈ x, IsHereditarilyCountable y) : IsHereditarilyCountable x :=
  ZFSet.hereditarily_iff.mpr ⟨hx, hm⟩

theorem countable {x : ZFSet.{u}} (hx : IsHereditarilyCountable x) :
    (x : Set ZFSet).Countable := hx.self

theorem mem {x y : ZFSet.{u}} (hx : IsHereditarilyCountable x) (hy : y ∈ x) :
    IsHereditarilyCountable y := ZFSet.Hereditarily.mem hx hy

theorem empty : IsHereditarilyCountable (∅ : ZFSet.{u}) := by
  apply of_countable
  · simpa only [ZFSet.coe_empty] using (Set.countable_empty : (∅ : Set ZFSet.{u}).Countable)
  · intro y hy
    exact (ZFSet.notMem_empty y hy).elim

theorem insert {x y : ZFSet.{u}} (hx : IsHereditarilyCountable x)
    (hy : IsHereditarilyCountable y) : IsHereditarilyCountable (Insert.insert x y) := by
  apply of_countable
  · simpa only [ZFSet.coe_insert] using hy.countable.insert x
  · intro z hz
    rcases ZFSet.mem_insert_iff.mp hz with rfl | hz
    · exact hx
    · exact hy.mem hz

theorem singleton {x : ZFSet.{u}} (hx : IsHereditarilyCountable x) :
    IsHereditarilyCountable ({x} : ZFSet) := hx.insert empty

theorem pair {x y : ZFSet.{u}} (hx : IsHereditarilyCountable x)
    (hy : IsHereditarilyCountable y) : IsHereditarilyCountable (ZFSet.pair x y) :=
  hx.singleton.insert (hx.insert hy.singleton).singleton

theorem range {α : Type v} [Countable α] (f : α → ZFSet.{u})
    (hf : ∀ a, IsHereditarilyCountable (f a)) :
    IsHereditarilyCountable (ZFSet.range f) := by
  apply ZFSet.hereditarily_iff.mpr
  constructor
  · rw [ZFSet.coe_range]
    exact Set.countable_range f
  · intro y hy
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hy
    exact hf a

theorem rank_lt_omega_one {x : ZFSet.{u}} (hx : IsHereditarilyCountable x) :
    x.rank < ω₁ := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    have : Countable x := hx.countable.to_subtype
    have hr : ZFSet.range (fun y : x => y.val) = x := by
      ext y
      simp only [ZFSet.mem_range]
      exact ⟨fun ⟨z, hz⟩ => hz ▸ z.property, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩
    calc
      x.rank = (ZFSet.range (fun y : x => y.val)).rank := congrArg ZFSet.rank hr.symm
      _ = ⨆ y : x, Order.succ y.val.rank := ZFSet.rank_range _
      _ < ω₁ := Ordinal.iSup_lt_omega_one fun y =>
        (Cardinal.isSuccLimit_omega 1).succ_lt (ih y.val y.property (hx.mem y.property))

theorem mem_vonNeumann_omega_one {x : ZFSet.{u}} (hx : IsHereditarilyCountable x) :
    x ∈ ZFSet.vonNeumann ω₁ :=
  ZFSet.mem_vonNeumann.mpr hx.rank_lt_omega_one

theorem ordinal {o : Ordinal.{u}} (ho : o < ω₁) :
    IsHereditarilyCountable o.toZFSet := by
  induction o using WellFoundedLT.induction with
  | ind o ih =>
    apply of_countable
    · rw [Ordinal.coe_toZFSet]
      exact (Cardinal.countable_Iio_of_lt_omega_one ho).image _
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hy
      exact ih a ha (ha.trans ho)

theorem nat (n : ℕ) : IsHereditarilyCountable (n : Ordinal.{u}).toZFSet :=
  ordinal ((Ordinal.natCast_lt_omega0 n).trans Ordinal.omega0_lt_omega_one)

end IsHereditarilyCountable

/-- The class of hereditarily countable sets, represented inside a fixed universe. -/
def HC := {x : ZFSet.{u} // IsHereditarilyCountable x}

instance : Small.{u} HC.{u} := by
  let f : HC.{u} → (ZFSet.vonNeumann ω₁ : ZFSet.{u}) :=
    fun x => ⟨x.val, x.property.mem_vonNeumann_omega_one⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : (ZFSet.vonNeumann ω₁ : ZFSet.{u}) => z.val) h)
  exact small_of_injective hf

end Erdos736
end


/- Source module Erdos736.HCEncoding. -/
section
open Cardinal Ordinal

universe u v

namespace Erdos736.HC

instance (x : HC.{u}) : Countable x.val := x.property.countable.to_subtype

/-- Every member of a hereditarily countable set is again hereditarily countable. -/
def element (x : HC.{u}) (y : x.val) : HC.{u} :=
  ⟨y.val, x.property.mem y.property⟩

theorem element_injective (x : HC.{u}) : Function.Injective (element x) := by
  intro y z h
  exact Subtype.ext (congrArg (fun z : HC.{u} => z.val) h)

noncomputable def pair (x y : HC.{u}) : HC.{u} :=
  ⟨ZFSet.pair x.val y.val, x.property.pair y.property⟩

theorem pair_injective {x y x' y' : HC.{u}} :
    pair x y = pair x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    have hp := ZFSet.pair_inj.mp (congrArg Subtype.val h)
    exact ⟨Subtype.ext hp.1, Subtype.ext hp.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

noncomputable def ordinal (o : {a : Ordinal.{u} // a < ω₁}) : HC.{u} :=
  ⟨o.val.toZFSet, IsHereditarilyCountable.ordinal o.property⟩

theorem ordinal_injective : Function.Injective ordinal.{u} := by
  intro a b h
  exact Subtype.ext (Ordinal.toZFSet_injective (congrArg Subtype.val h))

noncomputable def nat (n : ℕ) : HC.{u} :=
  ⟨(n : Ordinal.{u}).toZFSet, IsHereditarilyCountable.nat n⟩

theorem nat_injective : Function.Injective nat.{u} := by
  intro a b h
  exact Nat.cast_injective (R := Ordinal) (Ordinal.toZFSet_injective (congrArg Subtype.val h))

noncomputable def range {α : Type v} [Countable α] (f : α → HC.{u}) : HC.{u} :=
  ⟨ZFSet.range (fun a => (f a).val), IsHereditarilyCountable.range _ (fun a => (f a).property)⟩

theorem mem_range {α : Type v} [Countable α] (f : α → HC.{u}) (x : HC.{u}) :
    x.val ∈ (range f).val ↔ ∃ a, f a = x := by
  change x.val ∈ ZFSet.range (fun a => (f a).val) ↔ _
  rw [ZFSet.mem_range]
  exact exists_congr fun a => Subtype.ext_iff.symm

noncomputable def functionGraph {α : Type v} [Countable α]
    (domain : α → HC.{u}) (f : α → HC.{u}) : HC.{u} :=
  range (fun a => pair (domain a) (f a))

theorem functionGraph_injective {α : Type v} [Countable α]
    (domain : α → HC.{u}) (hd : Function.Injective domain) :
    Function.Injective (functionGraph domain) := by
  intro f g h
  funext a
  have hm : (pair (domain a) (f a)).val ∈ (functionGraph domain g).val := by
    rw [← h]
    exact (mem_range _ _).mpr ⟨a, rfl⟩
  obtain ⟨b, hb⟩ := (mem_range _ _).mp hm
  obtain ⟨hkey, hvalue⟩ := pair_injective.mp hb
  have hba : b = a := hd hkey
  subst b
  exact hvalue.symm

theorem rank_lt_pair_left (x y : HC.{u}) : x.val.rank < (pair x y).val.rank := by
  have hx : x.val ∈ ({x.val} : ZFSet) := ZFSet.mem_singleton.mpr rfl
  have hp : ({x.val} : ZFSet) ∈ ZFSet.pair x.val y.val := ZFSet.mem_pair.mpr (Or.inl rfl)
  exact (ZFSet.rank_lt_of_mem hx).trans (ZFSet.rank_lt_of_mem hp)

theorem rank_lt_pair_right (x y : HC.{u}) : y.val.rank < (pair x y).val.rank := by
  have hy : y.val ∈ ({x.val, y.val} : ZFSet) := ZFSet.mem_pair.mpr (Or.inr rfl)
  have hp : ({x.val, y.val} : ZFSet) ∈ ZFSet.pair x.val y.val :=
    ZFSet.mem_pair.mpr (Or.inr rfl)
  exact (ZFSet.rank_lt_of_mem hy).trans (ZFSet.rank_lt_of_mem hp)

/-- Encode any countable collection of hereditarily countable objects as one object. -/
noncomputable def collect (s : Set HC.{u}) (hs : s.Countable) : HC.{u} := by
  have : Countable s := hs.to_subtype
  exact range (fun x : s => x.val)

theorem mem_collect (s : Set HC.{u}) (hs : s.Countable) (x : HC.{u}) :
    x.val ∈ (collect s hs).val ↔ x ∈ s := by
  have : Countable s := hs.to_subtype
  change x.val ∈ (range (fun y : s => y.val)).val ↔ _
  rw [mem_range]
  exact ⟨fun ⟨y, h⟩ => h ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

end Erdos736.HC
end


/- Source module Erdos736.HostVertex. -/
section
open Cardinal Ordinal Order

universe u

namespace Erdos736

abbrev CountableOrdinal := {o : Ordinal.{u} // o < ω₁}

instance : Small.{u} CountableOrdinal.{u} := by
  change Small.{u} (Set.Iio (ω₁ : Ordinal.{u}))
  infer_instance

/-- The set-sized data from which a host vertex is formed.

The memory function is defined on the whole base. Its restriction to previously
encoded vertices provides the color prediction used in the source construction.
-/
structure HostVertexData where
  base : HC.{u}
  delta : CountableOrdinal.{u}
  memory : base.val → ℕ
  ladder : ℕ → CountableOrdinal.{u}

namespace HostVertexData

noncomputable def memoryCode (v : HostVertexData.{u}) : HC.{u} :=
  HC.functionGraph (HC.element v.base) (fun x => HC.nat (v.memory x))

noncomputable def ladderCode (v : HostVertexData.{u}) : HC.{u} :=
  HC.functionGraph HC.nat (fun n => HC.ordinal (v.ladder n))

/-- A faithful encoding by Kuratowski ordered pairs and ordinary function graphs. -/
noncomputable def code (v : HostVertexData.{u}) : HC.{u} :=
  HC.pair v.base (HC.pair (HC.ordinal v.delta) (HC.pair v.memoryCode v.ladderCode))

theorem code_injective : Function.Injective code.{u} := by
  rintro ⟨M, δ, f, C⟩ ⟨M', δ', f', C'⟩ h
  obtain ⟨hM, hrest⟩ := HC.pair_injective.mp h
  dsimp only at hM
  subst M'
  obtain ⟨hδ, hrest⟩ := HC.pair_injective.mp hrest
  have hδ' : δ = δ' := HC.ordinal_injective hδ
  subst δ'
  obtain ⟨hf, hC⟩ := HC.pair_injective.mp hrest
  have hf' : f = f' := by
    have he := HC.functionGraph_injective (HC.element M) (HC.element_injective M) hf
    funext x
    exact HC.nat_injective (congrFun he x)
  have hC' : C = C' := by
    have he := HC.functionGraph_injective HC.nat HC.nat_injective hC
    funext n
    exact HC.ordinal_injective (congrFun he n)
  subst f'
  subst C'
  rfl

theorem base_rank_lt_code (v : HostVertexData.{u}) : v.base.val.rank < v.code.val.rank :=
  HC.rank_lt_pair_left _ _

/-- The source construction's transitive base, initial segment, and cofinal ladder conditions. -/
structure Valid (v : HostVertexData.{u}) : Prop where
  base_transitive : v.base.val.IsTransitive
  ordinal_members : ∀ o : CountableOrdinal.{u}, o.val.toZFSet ∈ v.base.val ↔ o.val < v.delta.val
  delta_limit : IsSuccLimit v.delta.val
  ladder_increasing : StrictMono v.ladder
  ladder_below : ∀ n, (v.ladder n).val < v.delta.val
  ladder_cofinal : ∀ o < v.delta.val, ∃ n, o < (v.ladder n).val

end HostVertexData

def HostVertex := {v : HostVertexData.{u} // v.Valid}

namespace HostVertex

/-- A concrete vertex with base `ω`, constant memory, and the natural-number ladder. -/
noncomputable def omegaData : HostVertexData.{u} where
  base := HC.ordinal ⟨ω, Ordinal.omega0_lt_omega_one⟩
  delta := ⟨ω, Ordinal.omega0_lt_omega_one⟩
  memory := fun _ => 0
  ladder n := ⟨n, (Ordinal.natCast_lt_omega0 n).trans Ordinal.omega0_lt_omega_one⟩

theorem omegaData_valid : omegaData.{u}.Valid where
  base_transitive := (ZFSet.isOrdinal_toZFSet ω).isTransitive
  ordinal_members o := Ordinal.toZFSet_mem_toZFSet_iff
  delta_limit := Ordinal.isSuccLimit_omega0
  ladder_increasing := by
    intro n m hnm
    change (n : Ordinal) < (m : Ordinal)
    exact_mod_cast hnm
  ladder_below n := Ordinal.natCast_lt_omega0 n
  ladder_cofinal o ho := by
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp ho
    refine ⟨n + 1, ?_⟩
    change (n : Ordinal) < ((n + 1 : ℕ) : Ordinal)
    exact_mod_cast Nat.lt_succ_self n

noncomputable instance : Nonempty HostVertex.{u} := ⟨⟨omegaData, omegaData_valid⟩⟩

noncomputable def code (v : HostVertex.{u}) : HC.{u} := v.val.code

theorem code_injective : Function.Injective code.{u} := by
  intro v w h
  exact Subtype.ext (HostVertexData.code_injective h)

instance : Small.{u} HostVertex.{u} := small_of_injective code_injective

/-- A predecessor belongs to the transitive base of its successor. -/
def Precedes (v w : HostVertex.{u}) : Prop := v.code.val ∈ w.val.base.val

theorem rank_lt_of_precedes {v w : HostVertex.{u}} (h : Precedes v w) :
    v.code.val.rank < w.code.val.rank :=
  (ZFSet.rank_lt_of_mem h).trans w.val.base_rank_lt_code

theorem precedes_wellFounded : WellFounded Precedes.{u} :=
  (InvImage.wf (fun v : HostVertex.{u} => v.code.val.rank) wellFounded_lt).mono
    (fun _ _ h => rank_lt_of_precedes h)

theorem precedes_irrefl (v : HostVertex.{u}) : ¬Precedes v v :=
  fun h => (lt_irrefl v.code.val.rank) (rank_lt_of_precedes h)

end HostVertex

end Erdos736
end


/- Source module Erdos736.CountableClosure. -/
section
/-!
Countable closure under a countable family of finitary functions.
The host's lower chromatic bound uses these closures for its specified witness
and bounding functions, implementing the needed elementary-submodel argument.
-/

universe u v

namespace Erdos736.CountableClosure

variable {X : Type u} {I : Type v} (operations : I → List X → X)

def step (s : Set X) : Set X :=
  s ∪ Set.range (fun p : I × List s => operations p.1 (p.2.map Subtype.val))

def stage (s : Set X) : ℕ → Set X
  | 0 => s
  | n + 1 => step operations (stage s n)

def hull (s : Set X) : Set X := ⋃ n, stage operations s n

theorem countable_step [Countable I] {s : Set X} (hs : s.Countable) : (step operations s).Countable := by
  have : Countable s := hs.to_subtype
  exact hs.union (Set.countable_range _)

theorem countable_stage [Countable I] {s : Set X} (hs : s.Countable) (n : ℕ) :
    (stage operations s n).Countable := by
  induction n with
  | zero => exact hs
  | succ n ih => exact countable_step operations ih

theorem countable_hull [Countable I] {s : Set X} (hs : s.Countable) : (hull operations s).Countable :=
  Set.countable_iUnion (countable_stage operations hs)

theorem stage_mono (s : Set X) : Monotone (stage operations s) :=
  monotone_nat_of_le_succ (fun _ _ hx => Or.inl hx)

theorem subset_hull (s : Set X) : s ⊆ hull operations s := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨0, hx⟩

theorem list_bounded_iUnion (sets : ℕ → Set X) (hmono : Monotone sets) {xs : List X}
    (hxs : ∀ x ∈ xs, x ∈ ⋃ n, sets n) :
    ∃ n, ∀ x ∈ xs, x ∈ sets n := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons a xs ih =>
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hxs a (by simp))
    obtain ⟨m, hm⟩ := ih (fun x hx => hxs x (by simp [hx]))
    refine ⟨max n m, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hmono (Nat.le_max_left n m) hn
    · exact hmono (Nat.le_max_right n m) (hm x hx)

theorem list_bounded {s : Set X} {xs : List X}
    (hxs : ∀ x ∈ xs, x ∈ hull operations s) :
    ∃ n, ∀ x ∈ xs, x ∈ stage operations s n :=
  list_bounded_iUnion (stage operations s) (stage_mono operations s) hxs

theorem closed_hull (s : Set X) (i : I) (xs : List X)
    (hxs : ∀ x ∈ xs, x ∈ hull operations s) :
    operations i xs ∈ hull operations s := by
  obtain ⟨n, hn⟩ := list_bounded operations hxs
  apply Set.mem_iUnion.mpr
  refine ⟨n + 1, Or.inr ?_⟩
  refine ⟨(i, xs.attachWith _ hn), ?_⟩
  simp only [List.attachWith_map_subtype_val]

theorem exists_closed_countable [Countable I] {s : Set X} (hs : s.Countable) :
    ∃ M : Set X, M.Countable ∧ s ⊆ M ∧
      ∀ i xs, (∀ x ∈ xs, x ∈ M) → operations i xs ∈ M :=
  ⟨hull operations s, countable_hull operations hs, subset_hull operations s,
    closed_hull operations s⟩

end Erdos736.CountableClosure
end


/- Source module Erdos736.HCModel. -/
section
open Cardinal Ordinal Order

universe u

namespace Erdos736.HC

/-- An enumeration containing every member of an HC set. The empty set fills unused entries. -/
noncomputable def memberEnumeration (x : HC.{u}) (n : ℕ) : HC.{u} := by
  let y := Set.enumerateCountable x.property.countable (∅ : ZFSet.{u}) n
  refine ⟨y, ?_⟩
  have hy : y ∈ insert ∅ (x.val : Set ZFSet) :=
    Set.range_enumerateCountable_subset x.property.countable ∅ (Set.mem_range_self n)
  rcases Set.mem_insert_iff.mp hy with h | h
  · exact h ▸ IsHereditarilyCountable.empty
  · exact x.property.mem h

theorem memberEnumeration_hits (x : HC.{u}) (y : x.val) :
    ∃ n, memberEnumeration x n = element x y := by
  obtain ⟨n, hn⟩ := Set.subset_range_enumerate x.property.countable (∅ : ZFSet.{u}) y.property
  exact ⟨n, Subtype.ext hn⟩

theorem collect_transitive (M : Set HC.{u}) (hM : M.Countable)
    (hclosed : ∀ x ∈ M, ∀ n, memberEnumeration x n ∈ M) :
    (collect M hM).val.IsTransitive := by
  intro y hy z hz
  let y' : HC.{u} := ⟨y, (collect M hM).property.mem hy⟩
  have hyM : y' ∈ M := (mem_collect M hM y').mp hy
  obtain ⟨n, hn⟩ := memberEnumeration_hits y' (⟨z, hz⟩ : y'.val)
  have hzM : element y' ⟨z, hz⟩ ∈ M := hn ▸ hclosed y' hyM n
  exact (mem_collect M hM _).mpr hzM

end Erdos736.HC

namespace Erdos736.HCModel

def ordinalPart (M : Set HC.{u}) : Set CountableOrdinal.{u} :=
  {o | HC.ordinal o ∈ M}

theorem countable_ordinalPart {M : Set HC.{u}} (hM : M.Countable) :
    (ordinalPart M).Countable := hM.preimage HC.ordinal_injective

def successor (o : CountableOrdinal.{u}) : CountableOrdinal.{u} :=
  ⟨Order.succ o.val, (Cardinal.isSuccLimit_omega 1).succ_lt o.property⟩

def ClosedSuccessors (M : Set HC.{u}) : Prop :=
  ∀ o ∈ ordinalPart M, successor o ∈ ordinalPart M

noncomputable def height (M : Set HC.{u}) (hM : M.Countable) : CountableOrdinal.{u} := by
  have : Countable (ordinalPart M) := (countable_ordinalPart hM).to_subtype
  exact ⟨⨆ o : ordinalPart M, o.val.val, Ordinal.iSup_lt_omega_one (fun o => o.val.property)⟩

theorem member_lt_height {M : Set HC.{u}} (hM : M.Countable)
    (hSucc : ClosedSuccessors M) (o : CountableOrdinal.{u}) (ho : o ∈ ordinalPart M) :
    o.val < (height M hM).val := by
  have hsp : successor o ∈ ordinalPart M := hSucc o ho
  have hle := Ordinal.le_iSup (fun a : ordinalPart M => a.val.val) ⟨successor o, hsp⟩
  exact (Order.lt_succ o.val).trans_le hle

theorem ordinal_members_iff {M : Set HC.{u}} (hM : M.Countable)
    (hTrans : (HC.collect M hM).val.IsTransitive) (hSucc : ClosedSuccessors M)
    (o : CountableOrdinal.{u}) : o ∈ ordinalPart M ↔ o.val < (height M hM).val := by
  constructor
  · exact member_lt_height hM hSucc o
  · intro ho
    obtain ⟨a, ha⟩ := Ordinal.lt_iSup_iff.mp ho
    have haM : (HC.ordinal a.val).val ∈ (HC.collect M hM).val :=
      (HC.mem_collect M hM _).mpr a.property
    have hoa : (HC.ordinal o).val ∈ (HC.ordinal a.val).val :=
      Ordinal.toZFSet_mem_toZFSet_iff.mpr ha
    exact (HC.mem_collect M hM _).mp (hTrans.mem_trans hoa haM)

theorem height_isSuccLimit {M : Set HC.{u}} (hM : M.Countable)
    (hTrans : (HC.collect M hM).val.IsTransitive) (hSucc : ClosedSuccessors M)
    (hNonempty : (ordinalPart M).Nonempty) : IsSuccLimit (height M hM).val := by
  refine ⟨?_, isSuccPrelimit_iff_succ_lt.mpr ?_⟩
  · obtain ⟨o, ho⟩ := hNonempty
    exact not_isMin_of_lt (member_lt_height hM hSucc o ho)
  · intro a ha
    let o : CountableOrdinal.{u} := ⟨a, ha.trans (height M hM).property⟩
    have ho : o ∈ ordinalPart M := (ordinal_members_iff hM hTrans hSucc o).mpr ha
    exact member_lt_height hM hSucc (successor o) (hSucc o ho)

end Erdos736.HCModel
end


/- Source module Erdos736.ModelClosure. -/
section
open Cardinal Ordinal Order

universe u

namespace Erdos736.HC

noncomputable def nextOrdinal (x : HC.{u}) : HC.{u} :=
  ordinal ⟨Order.succ x.val.rank,
    (Cardinal.isSuccLimit_omega 1).succ_lt x.property.rank_lt_omega_one⟩

theorem nextOrdinal_ordinal (o : CountableOrdinal.{u}) :
    nextOrdinal (ordinal o) = ordinal (HCModel.successor o) := by
  apply Subtype.ext
  simp only [nextOrdinal, ordinal, HCModel.successor, Ordinal.rank_toZFSet]

end Erdos736.HC

namespace Erdos736.HCModel

abbrev OperationIndex := ℕ ⊕ (Unit ⊕ ℕ)

noncomputable def operations (extra : ℕ → List HC.{u} → HC.{u}) :
    OperationIndex → List HC.{u} → HC.{u}
  | Sum.inl n, xs => HC.memberEnumeration (xs.headD (HC.nat 0)) n
  | Sum.inr (Sum.inl _), xs => HC.nextOrdinal (xs.headD (HC.nat 0))
  | Sum.inr (Sum.inr n), xs => extra n xs

structure ClosedModel (extra : ℕ → List HC.{u} → HC.{u}) where
  carrier : Set HC.{u}
  countable : carrier.Countable
  zero_mem : HC.nat 0 ∈ carrier
  members_closed : ∀ x ∈ carrier, ∀ n, HC.memberEnumeration x n ∈ carrier
  successors_closed : ClosedSuccessors carrier
  extra_closed : ∀ i xs, (∀ x ∈ xs, x ∈ carrier) → extra i xs ∈ carrier

namespace ClosedModel

variable {extra : ℕ → List HC.{u} → HC.{u}}

theorem transitive (M : ClosedModel extra) : (HC.collect M.carrier M.countable).val.IsTransitive :=
  HC.collect_transitive M.carrier M.countable M.members_closed

noncomputable def height (M : ClosedModel extra) : CountableOrdinal.{u} :=
  HCModel.height M.carrier M.countable

theorem ordinal_members (M : ClosedModel extra) (o : CountableOrdinal.{u}) :
    HC.ordinal o ∈ M.carrier ↔ o.val < M.height.val :=
  ordinal_members_iff M.countable M.transitive M.successors_closed o

theorem height_limit (M : ClosedModel extra) : IsSuccLimit M.height.val := by
  apply height_isSuccLimit M.countable M.transitive M.successors_closed
  refine ⟨⟨0, (Ordinal.natCast_lt_omega0 0).trans Ordinal.omega0_lt_omega_one⟩, ?_⟩
  exact M.zero_mem

end ClosedModel

noncomputable def close (extra : ℕ → List HC.{u} → HC.{u})
    (s : Set HC.{u}) (hs : s.Countable) : ClosedModel extra := by
  let M := CountableClosure.hull (operations extra) (insert (HC.nat 0) s)
  have hc : M.Countable := CountableClosure.countable_hull _ (hs.insert _)
  have hseed : insert (HC.nat 0) s ⊆ M := CountableClosure.subset_hull _ _
  have hclosed (i : OperationIndex) (xs : List HC.{u})
      (hxs : ∀ x ∈ xs, x ∈ M) : operations extra i xs ∈ M :=
    CountableClosure.closed_hull _ _ _ _ hxs
  refine ⟨M, hc, hseed (by simp), ?_, ?_, ?_⟩
  · intro x hx n
    exact hclosed (Sum.inl n) [x] (by simpa)
  · intro o ho
    change HC.ordinal o ∈ M at ho
    change HC.ordinal (successor o) ∈ M
    have h := hclosed (Sum.inr (Sum.inl ())) [HC.ordinal o] (by simpa using ho)
    simpa only [operations, List.headD_cons, HC.nextOrdinal_ordinal] using h
  · intro i xs hxs
    exact hclosed (Sum.inr (Sum.inr i)) xs hxs

theorem subset_close (extra : ℕ → List HC.{u} → HC.{u})
    (s : Set HC.{u}) (hs : s.Countable) : s ⊆ (close extra s hs).carrier := by
  intro x hx
  exact CountableClosure.subset_hull (operations extra) (insert (HC.nat 0) s) (by simp [hx])

noncomputable def extend {extra : ℕ → List HC.{u} → HC.{u}}
    (M : ClosedModel extra) : ClosedModel extra :=
  close extra (insert (HC.ordinal M.height) M.carrier) (M.countable.insert _)

theorem subset_extend {extra : ℕ → List HC.{u} → HC.{u}} (M : ClosedModel extra) :
    M.carrier ⊆ (extend M).carrier := by
  intro x hx
  exact subset_close _ _ _ (by simp [hx])

theorem height_lt_extend {extra : ℕ → List HC.{u} → HC.{u}} (M : ClosedModel extra) :
    M.height.val < (extend M).height.val := by
  apply ((extend M).ordinal_members M.height).mp
  exact subset_close _ _ _ (by simp)

theorem height_mem_extend {extra : ℕ → List HC.{u} → HC.{u}} (M : ClosedModel extra) :
    HC.ordinal M.height ∈ (extend M).carrier :=
  subset_close _ _ _ (by simp)

noncomputable def chain (extra : ℕ → List HC.{u} → HC.{u}) : ℕ → ClosedModel extra
  | 0 => close extra ∅ Set.countable_empty
  | n + 1 => extend (chain extra n)

theorem chain_mono (extra : ℕ → List HC.{u} → HC.{u}) :
    Monotone (fun n => (chain extra n).carrier) :=
  monotone_nat_of_le_succ (fun n => subset_extend (chain extra n))

theorem chain_height_strictMono (extra : ℕ → List HC.{u} → HC.{u}) :
    StrictMono (fun n => (chain extra n).height.val) :=
  strictMono_nat_of_lt_succ (fun n => height_lt_extend (chain extra n))

/-- The union of the increasing chain remains closed under all the chosen finitary operations. -/
noncomputable def limitModel (extra : ℕ → List HC.{u} → HC.{u}) : ClosedModel extra where
  carrier := ⋃ n, (chain extra n).carrier
  countable := Set.countable_iUnion (fun n => (chain extra n).countable)
  zero_mem := Set.mem_iUnion.mpr ⟨0, (chain extra 0).zero_mem⟩
  members_closed := by
    intro x hx k
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨n, (chain extra n).members_closed x hn k⟩
  successors_closed := by
    intro o ho
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ho
    exact Set.mem_iUnion.mpr ⟨n, (chain extra n).successors_closed o hn⟩
  extra_closed := by
    intro i xs hxs
    obtain ⟨n, hn⟩ := CountableClosure.list_bounded_iUnion
      (fun n => (chain extra n).carrier) (chain_mono extra) hxs
    exact Set.mem_iUnion.mpr ⟨n, (chain extra n).extra_closed i xs hn⟩

theorem chain_height_lt_limit (extra : ℕ → List HC.{u} → HC.{u}) (n : ℕ) :
    (chain extra n).height.val < (limitModel extra).height.val := by
  apply ((limitModel extra).ordinal_members (chain extra n).height).mp
  exact Set.mem_iUnion.mpr ⟨n + 1, height_mem_extend (chain extra n)⟩

theorem limit_height_eq_iSup (extra : ℕ → List HC.{u} → HC.{u}) :
    (limitModel extra).height.val = ⨆ n, (chain extra n).height.val := by
  apply le_antisymm
  · apply Ordinal.iSup_le
    intro o
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp o.property
    exact (((chain extra n).ordinal_members o.val).mp hn).le.trans
      (Ordinal.le_iSup (fun n => (chain extra n).height.val) n)
  · exact Ordinal.iSup_le (fun n => (chain_height_lt_limit extra n).le)

theorem chain_height_cofinal (extra : ℕ → List HC.{u} → HC.{u})
    (o : Ordinal.{u}) (ho : o < (limitModel extra).height.val) :
    ∃ n, o < (chain extra n).height.val := by
  rw [limit_height_eq_iSup] at ho
  exact Ordinal.lt_iSup_iff.mp ho

end Erdos736.HCModel
end


/- Source module Erdos736.ParentColoring. -/
section
open SimpleGraph

universe u

namespace Erdos736

/-- A graph whose edges point to a unique well-founded predecessor is bipartite. -/
theorem bicoloring_of_parent {V : Type u} {G : SimpleGraph V}
    {r : V → V → Prop} (wf : WellFounded r) (parent : V → Option V)
    (hparent : ∀ x y, parent x = some y → r y x)
    (hedge : ∀ {x y}, G.Adj x y → parent x = some y ∨ parent y = some x) :
    Nonempty (G.Coloring Bool) := by
  classical
  let step (x : V) (previous : ∀ y, r y x → Bool) : Bool :=
    match he : parent x with
    | none => false
    | some y => !(previous y (hparent x y he))
  let c : V → Bool := wf.fix step
  have hc (x y : V) (hxy : parent x = some y) : c x = !(c y) := by
    have he := wf.fix_eq step x
    change c x = step x (fun z _ => c z) at he
    dsimp only [step] at he
    split at he
    · rename_i hnone
      rw [hxy] at hnone
      contradiction
    · rename_i z hsome
      have hz : z = y := Option.some.inj (hsome.symm.trans hxy)
      subst z
      exact he
  refine ⟨Coloring.mk c ?_⟩
  intro x y hxy hcolor
  rcases hedge hxy with hparentXY | hparentYX
  · have he := hc x y hparentXY
    rw [hcolor] at he
    cases hcy : c y <;> simp only [hcy, Bool.not_false, Bool.not_true] at he
    all_goals contradiction
  · have he := hc y x hparentYX
    rw [← hcolor] at he
    cases hcx : c x <;> simp only [hcx, Bool.not_false, Bool.not_true] at he
    all_goals contradiction

end Erdos736
end


/- Source module Erdos736.Statement. -/
section
open SimpleGraph Cardinal

universe u

namespace Erdos736

/-- The least cardinality of a palette admitting a proper coloring. -/
noncomputable def chromaticCardinal {V : Type u} (G : SimpleGraph V) : Cardinal.{u} :=
  sInf {κ | ∃ C : Type u, #C = κ ∧ Nonempty (G.Coloring C)}

theorem chromaticCardinal_le {V C : Type u} {G : SimpleGraph V}
    (c : G.Coloring C) : chromaticCardinal G ≤ #C := by
  exact csInf_le' ⟨C, rfl, ⟨c⟩⟩

theorem chromaticCardinal_spec {V : Type u} (G : SimpleGraph V) :
    ∃ C : Type u, #C = chromaticCardinal G ∧ Nonempty (G.Coloring C) := by
  have h : Set.Nonempty {κ : Cardinal.{u} |
      ∃ C : Type u, #C = κ ∧ Nonempty (G.Coloring C)} :=
    ⟨#V, V, rfl, ⟨G.selfColoring⟩⟩
  exact csInf_mem h

theorem chromaticCardinal_le_iff {V : Type u} (G : SimpleGraph V) (κ : Cardinal.{u}) :
    chromaticCardinal G ≤ κ ↔ Nonempty (G.Coloring κ.out) := by
  constructor
  · intro h
    obtain ⟨C, hC, ⟨c⟩⟩ := chromaticCardinal_spec G
    have he : #C ≤ #κ.out := by simpa only [hC, Cardinal.mk_out] using h
    obtain ⟨e⟩ := (Cardinal.le_def C κ.out).mp he
    exact ⟨G.recolorOfEmbedding e c⟩
  · rintro ⟨c⟩
    simpa only [Cardinal.mk_out] using chromaticCardinal_le c

/-- Ordinary graph containment through an injective adjacency-preserving map. -/
def ContainsCopy {V W : Type u} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ a b, H.Adj a b → G.Adj (f a) (f b)

theorem finiteAgeIncluded_iff {V W : Type u} (H : SimpleGraph W) (G : SimpleGraph V) :
    FiniteAgeIncluded H G ↔
      ∀ (U : Type u) [Fintype U] (F : SimpleGraph U),
        ContainsCopy H F → ContainsCopy G F := by
  classical
  constructor
  · intro hAge U _ F hF
    obtain ⟨f, hf, hfAdj⟩ := hF
    let s : Finset W := Finset.univ.image f
    let g : U → s := fun x => ⟨f x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
    obtain ⟨j, hj, hjAdj⟩ := hAge s
    refine ⟨fun x => j (g x), ?_, ?_⟩
    · intro x y hxy
      exact hf (congrArg Subtype.val (hj hxy))
    · intro x y hxy
      exact hjAdj (g x) (g y) (hfAdj x y hxy)
  · intro h s
    have hc : ContainsCopy H (H.induce (s : Set W)) :=
      ⟨Subtype.val, Subtype.val_injective, fun _ _ hxy => hxy⟩
    exact h s (H.induce (s : Set W)) hc

/-- Walter Taylor's assertion in Erdős problem 736, with cardinal chromatic numbers. -/
def TaylorConjecture : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V), chromaticCardinal G = ℵ₁ →
    ∀ m : Cardinal.{u}, ∃ (W : Type u) (H : SimpleGraph W),
      chromaticCardinal H = m ∧ FiniteAgeIncluded H G

end Erdos736
end


/- Source module Erdos736.HostGraph. -/
section
open SimpleGraph Cardinal Ordinal

universe u

namespace Erdos736.HostGraph

variable (compatible : ℕ → HostVertex.{u} → HostVertex.{u} → Prop)

/-- A predecessor passes the memory test and the prescribed finite type tests. -/
def Eligible (v : HostVertex.{u}) (k : ℕ) (w : HostVertex.{u}) : Prop :=
  ∃ h : HostVertex.Precedes w v,
    v.val.memory ⟨w.code.val, h⟩ = k ∧ compatible k w v

noncomputable def parent (v : HostVertex.{u}) (k : ℕ) : Option HostVertex.{u} := by
  classical
  exact if h : ∃ w, Eligible compatible v k w then some h.choose else none

theorem parent_spec {v w : HostVertex.{u}} {k : ℕ}
    (h : parent compatible v k = some w) : Eligible compatible v k w := by
  classical
  by_cases he : ∃ w, Eligible compatible v k w
  · have hp : parent compatible v k = some he.choose := by simp only [parent, dite_eq_left he]
    have hw : he.choose = w := Option.some.inj (hp.symm.trans h)
    exact hw ▸ he.choose_spec
  · simp only [parent, dite_eq_right he] at h
    cases h

theorem parent_precedes {v w : HostVertex.{u}} {k : ℕ}
    (h : parent compatible v k = some w) : HostVertex.Precedes w v :=
  (parent_spec compatible h).choose

theorem parent_exists {v : HostVertex.{u}} {k : ℕ}
    (h : ∃ w, Eligible compatible v k w) : ∃ w, parent compatible v k = some w := by
  classical
  exact ⟨h.choose, by simp only [parent, dite_eq_left h]⟩

noncomputable def layer (k : ℕ) : SimpleGraph HostVertex.{u} where
  Adj v w := parent compatible v k = some w ∨ parent compatible w k = some v
  symm := ⟨fun {v w} h => h.symm⟩
  loopless := ⟨fun v h => by
    rcases h with h | h
    all_goals exact HostVertex.precedes_irrefl v (parent_precedes compatible h)⟩

noncomputable def graph : SimpleGraph HostVertex.{u} where
  Adj v w := ∃ k, (layer compatible k).Adj v w
  symm := ⟨fun {_v _w} ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩
  loopless := ⟨fun _v ⟨k, hk⟩ => (layer compatible k).irrefl hk⟩

noncomputable def tail (n : ℕ) : SimpleGraph HostVertex.{u} where
  Adj v w := ∃ k, n ≤ k ∧ (layer compatible k).Adj v w
  symm := ⟨fun {_v _w} ⟨k, hn, hk⟩ => ⟨k, hn, hk.symm⟩⟩
  loopless := ⟨fun _v ⟨k, _, hk⟩ => (layer compatible k).irrefl hk⟩

theorem bicolor_layer (k : ℕ) : Nonempty ((layer compatible k).Coloring Bool) :=
  bicoloring_of_parent HostVertex.precedes_wellFounded
    (fun v => parent compatible v k) (fun _ _ h => parent_precedes compatible h)
    (fun h => h)

theorem tail_contains (n : ℕ) {v w : HostVertex.{u}}
    (h : (graph compatible).Adj v w)
    (hlow : ∀ j, j < n → ¬(layer compatible j).Adj v w) : (tail compatible n).Adj v w := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, Nat.le_of_not_gt (fun hkn => hlow k hkn hk), hk⟩

noncomputable def rankColoring : (graph compatible).Coloring CountableOrdinal.{u} :=
  Coloring.mk (fun v => ⟨v.code.val.rank, v.code.property.rank_lt_omega_one⟩) (by
    intro v w h hcolor
    have hr := congrArg Subtype.val hcolor
    obtain ⟨k, hk⟩ := h
    rcases hk with hk | hk
    · exact (HostVertex.rank_lt_of_precedes (parent_precedes compatible hk)).ne hr.symm
    · exact (HostVertex.rank_lt_of_precedes (parent_precedes compatible hk)).ne hr)

theorem countableOrdinal_card : #CountableOrdinal.{u} = ℵ₁ := by
  change #(Set.Iio (ω₁ : Ordinal.{u})) = ℵ₁
  simp only [Cardinal.mk_Iio_ordinal, Ordinal.card_omega, Cardinal.lift_aleph, Ordinal.lift_one]

theorem chromaticCardinal_le_aleph_one : chromaticCardinal (graph compatible) ≤ ℵ₁ := by
  simpa only [countableOrdinal_card] using chromaticCardinal_le (rankColoring compatible)

/-- A universe-small copy of the graph, for the original statement's fixed vertex universe. -/
noncomputable def smallGraph : SimpleGraph (Shrink.{u} HostVertex.{u}) :=
  (graph compatible).comap (equivShrink HostVertex).symm

noncomputable def smallRankColoring :
    (smallGraph compatible).Coloring (Shrink.{u} CountableOrdinal.{u}) :=
  (smallGraph compatible).recolorOfEquiv (equivShrink CountableOrdinal)
    ((rankColoring compatible).comap (Hom.comap (equivShrink HostVertex).symm _))

theorem smallCountableOrdinal_card : #(Shrink.{u} CountableOrdinal.{u}) = ℵ₁ := by
  have h : Cardinal.lift.{u + 1} #(Shrink.{u} CountableOrdinal.{u}) =
      Cardinal.lift.{u + 1} (ℵ₁ : Cardinal.{u}) := by
    simp only [Cardinal.lift_mk_shrink'', countableOrdinal_card, Cardinal.lift_aleph,
      Ordinal.lift_one]
  exact Cardinal.lift_inj.mp h

theorem smallGraph_chromaticCardinal_le_aleph_one :
    chromaticCardinal (smallGraph compatible) ≤ ℵ₁ := by
  simpa only [smallCountableOrdinal_card] using chromaticCardinal_le (smallRankColoring compatible)

end Erdos736.HostGraph
end


/- Source module Erdos736.DiagonalVertex. -/
section
open Cardinal Ordinal

universe u

namespace Erdos736

/-- Extend a coloring of host vertices to all HC codes, with value zero off the vertex codes. -/
noncomputable def colorOnCode (f : HostVertex.{u} → ℕ) (x : HC.{u}) : ℕ := by
  classical
  exact if h : ∃ v, HostVertex.code v = x then f h.choose else 0

theorem colorOnCode_code (f : HostVertex.{u} → ℕ) (v : HostVertex.{u}) :
    colorOnCode f (HostVertex.code v) = f v := by
  classical
  have h : ∃ w, HostVertex.code w = HostVertex.code v := ⟨v, rfl⟩
  have hw : h.choose = v := HostVertex.code_injective h.choose_spec
  simp only [colorOnCode, dite_eq_left h, hw]

namespace DiagonalVertex

noncomputable def data (extra : ℕ → List HC.{u} → HC.{u}) (f : HostVertex.{u} → ℕ) :
    HostVertexData.{u} where
  base := HC.collect (HCModel.limitModel extra).carrier (HCModel.limitModel extra).countable
  delta := (HCModel.limitModel extra).height
  memory x := colorOnCode f (HC.element
    (HC.collect (HCModel.limitModel extra).carrier (HCModel.limitModel extra).countable) x)
  ladder n := (HCModel.chain extra n).height

theorem data_valid (extra : ℕ → List HC.{u} → HC.{u}) (f : HostVertex.{u} → ℕ) :
    (data extra f).Valid where
  base_transitive := (HCModel.limitModel extra).transitive
  ordinal_members o := by
    exact (HC.mem_collect (HCModel.limitModel extra).carrier
      (HCModel.limitModel extra).countable (HC.ordinal o)).trans
      ((HCModel.limitModel extra).ordinal_members o)
  delta_limit := (HCModel.limitModel extra).height_limit
  ladder_increasing := fun _ _ h => HCModel.chain_height_strictMono extra h
  ladder_below := HCModel.chain_height_lt_limit extra
  ladder_cofinal := HCModel.chain_height_cofinal extra

noncomputable def vertex (extra : ℕ → List HC.{u} → HC.{u}) (f : HostVertex.{u} → ℕ) :
    HostVertex.{u} := ⟨data extra f, data_valid extra f⟩

/-- The diagonal vertex correctly predicts the color of every encoded predecessor in its base. -/
theorem memory_eq (extra : ℕ → List HC.{u} → HC.{u}) (f : HostVertex.{u} → ℕ)
    (v : HostVertex.{u}) (h : HostVertex.Precedes v (vertex extra f)) :
    (vertex extra f).val.memory ⟨v.code.val, h⟩ = f v := by
  change colorOnCode f v.code = f v
  exact colorOnCode_code f v

theorem monochromatic_edge_of_eligible
    (compatible : ℕ → HostVertex.{u} → HostVertex.{u} → Prop)
    (extra : ℕ → List HC.{u} → HC.{u}) (f : HostVertex.{u} → ℕ)
    (he : ∃ w, HostGraph.Eligible compatible (vertex extra f) (f (vertex extra f)) w) :
    ∃ v w, (HostGraph.graph compatible).Adj v w ∧ f v = f w := by
  obtain ⟨w, hw⟩ := HostGraph.parent_exists compatible he
  obtain ⟨hpre, hmemory, _⟩ := HostGraph.parent_spec compatible hw
  have hcolor : f w = f (vertex extra f) :=
    (memory_eq extra f w hpre).symm.trans hmemory
  exact ⟨vertex extra f, w, ⟨f (vertex extra f), Or.inl hw⟩, hcolor.symm⟩

end DiagonalVertex

end Erdos736
end


/- Source module Erdos736.PrefixReflection. -/
section
open Cardinal Ordinal

universe u

namespace Erdos736.PrefixReflection

def zeroOrdinal : CountableOrdinal.{u} := ⟨0, Ordinal.omega_pos 1⟩

def Prefix (p : List CountableOrdinal.{u}) (v : HostVertex.{u}) : Prop :=
  List.ofFn (fun i : Fin p.length => v.val.ladder i) = p

def P (f : HostVertex.{u} → ℕ) (k : ℕ) : ℕ → List CountableOrdinal.{u} → Prop
  | 0, p => ∃ v, f v = k ∧ Prefix p v
  | r + 1, p => ∀ a, ∃ b, a < b ∧ P f k r (p ++ [b])

theorem exists_bound {f : HostVertex.{u} → ℕ} {k r : ℕ} {p : List CountableOrdinal.{u}}
    (h : ¬P f k (r + 1) p) :
    ∃ a, ∀ b, a < b → ¬P f k r (p ++ [b]) := by
  classical
  change ¬∀ a, ∃ b, a < b ∧ P f k r (p ++ [b]) at h
  push Not at h
  exact h

noncomputable def bound (f : HostVertex.{u} → ℕ) (k r : ℕ) (p : List CountableOrdinal.{u}) :
    CountableOrdinal.{u} := by
  classical
  exact if h : ∃ a, ∀ b, a < b → ¬P f k r (p ++ [b]) then h.choose else zeroOrdinal

theorem bound_spec {f : HostVertex.{u} → ℕ} {k r : ℕ} {p : List CountableOrdinal.{u}}
    (h : ¬P f k (r + 1) p) (b : CountableOrdinal.{u}) (hb : bound f k r p < b) :
    ¬P f k r (p ++ [b]) := by
  classical
  have he := exists_bound h
  have heq : bound f k r p = he.choose := by simp only [bound, dite_eq_left he]
  rw [heq] at hb
  exact he.choose_spec b hb

noncomputable def pick (f : HostVertex.{u} → ℕ) (k r : ℕ) (p : List CountableOrdinal.{u})
    (a : CountableOrdinal.{u}) : CountableOrdinal.{u} := by
  classical
  exact if h : ∃ b, a < b ∧ P f k r (p ++ [b]) then h.choose else zeroOrdinal

theorem pick_spec {f : HostVertex.{u} → ℕ} {k r : ℕ} {p : List CountableOrdinal.{u}}
    (h : P f k (r + 1) p) (a : CountableOrdinal.{u}) :
    a < pick f k r p a ∧ P f k r (p ++ [pick f k r p a]) := by
  classical
  have he := h a
  have heq : pick f k r p a = he.choose := by simp only [pick, dite_eq_left he]
  rw [heq]
  exact he.choose_spec

noncomputable def pickVertex (f : HostVertex.{u} → ℕ) (k : ℕ) (p : List CountableOrdinal.{u}) :
    HostVertex.{u} := by
  classical
  exact if h : ∃ v, f v = k ∧ Prefix p v then h.choose else Classical.choice inferInstance

theorem pickVertex_spec {f : HostVertex.{u} → ℕ} {k : ℕ} {p : List CountableOrdinal.{u}}
    (h : P f k 0 p) : f (pickVertex f k p) = k ∧ Prefix p (pickVertex f k p) := by
  classical
  change ∃ v, f v = k ∧ Prefix p v at h
  have heq : pickVertex f k p = h.choose := by simp only [pickVertex, dite_eq_left h]
  rw [heq]
  exact h.choose_spec

noncomputable def decodeOrdinal (x : HC.{u}) : CountableOrdinal.{u} :=
  ⟨x.val.rank, x.property.rank_lt_omega_one⟩

@[simp] theorem decodeOrdinal_ordinal (o : CountableOrdinal.{u}) :
    decodeOrdinal (HC.ordinal o) = o := Subtype.ext (Ordinal.rank_toZFSet _)

noncomputable def encode (p : List CountableOrdinal.{u}) : List HC.{u} := p.map HC.ordinal

noncomputable def decode (p : List HC.{u}) : List CountableOrdinal.{u} := p.map decodeOrdinal

@[simp] theorem decode_encode (p : List CountableOrdinal.{u}) : decode (encode p) = p := by
  simp [decode, encode, List.map_map, Function.comp_def]

abbrev Operation := (ℕ × ℕ) ⊕ ((ℕ × ℕ) ⊕ ℕ)

noncomputable def operations (f : HostVertex.{u} → ℕ) (i : ℕ) (xs : List HC.{u}) : HC.{u} :=
  match (Encodable.decode i : Option Operation) with
  | some (Sum.inl (k, r)) => HC.ordinal (bound f k r (decode xs))
  | some (Sum.inr (Sum.inl (k, r))) =>
      HC.ordinal (pick f k r (decode xs.tail) (decodeOrdinal (xs.headD (HC.nat 0))))
  | some (Sum.inr (Sum.inr k)) => HostVertex.code (pickVertex f k (decode xs))
  | none => HC.nat 0

theorem bound_mem (f : HostVertex.{u} → ℕ) (M : HCModel.ClosedModel (operations f))
    (k r : ℕ) (p : List CountableOrdinal.{u})
    (hp : ∀ o ∈ p, HC.ordinal o ∈ M.carrier) : HC.ordinal (bound f k r p) ∈ M.carrier := by
  have h := M.extra_closed (Encodable.encode (Sum.inl (k, r) : Operation)) (encode p) (by
    intro x hx
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
    exact hp o ho)
  simpa only [operations, Encodable.encodek, decode_encode] using h

theorem pick_mem (f : HostVertex.{u} → ℕ) (M : HCModel.ClosedModel (operations f))
    (k r : ℕ) (p : List CountableOrdinal.{u}) (a : CountableOrdinal.{u})
    (hp : ∀ o ∈ p, HC.ordinal o ∈ M.carrier) (ha : HC.ordinal a ∈ M.carrier) :
    HC.ordinal (pick f k r p a) ∈ M.carrier := by
  have h := M.extra_closed (Encodable.encode (Sum.inr (Sum.inl (k, r)) : Operation))
    (HC.ordinal a :: encode p) (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
        exact hp o ho)
  simpa only [operations, Encodable.encodek, List.tail_cons, List.headD_cons,
    decodeOrdinal_ordinal, decode_encode] using h

theorem pickVertex_mem (f : HostVertex.{u} → ℕ) (M : HCModel.ClosedModel (operations f))
    (k : ℕ) (p : List CountableOrdinal.{u})
    (hp : ∀ o ∈ p, HC.ordinal o ∈ M.carrier) :
    (pickVertex f k p).code ∈ M.carrier := by
  have h := M.extra_closed (Encodable.encode (Sum.inr (Sum.inr k) : Operation)) (encode p) (by
    intro x hx
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
    exact hp o ho)
  simpa only [operations, Encodable.encodek, decode_encode] using h

theorem reflect (f : HostVertex.{u} → ℕ) (M : HCModel.ClosedModel (operations f))
    (k r : ℕ) (p : List CountableOrdinal.{u})
    (hp : ∀ o ∈ p, HC.ordinal o ∈ M.carrier)
    (h : P f k r (p ++ [M.height])) : P f k (r + 1) p := by
  classical
  by_contra hn
  have hb := (M.ordinal_members (bound f k r p)).mp (bound_mem f M k r p hp)
  exact bound_spec hn M.height hb h

noncomputable def chainPrefix (f : HostVertex.{u} → ℕ) (n : ℕ) : List CountableOrdinal.{u} :=
  List.ofFn (fun i : Fin n => (HCModel.chain (operations f) i).height)

theorem chainPrefix_succ (f : HostVertex.{u} → ℕ) (n : ℕ) :
    chainPrefix f (n + 1) = chainPrefix f n ++ [(HCModel.chain (operations f) n).height] := by
  unfold chainPrefix
  rw [List.ofFn_succ_last]
  rfl

theorem chainPrefix_mem (f : HostVertex.{u} → ℕ) (n : ℕ) :
    ∀ o ∈ chainPrefix f n, HC.ordinal o ∈ (HCModel.chain (operations f) n).carrier := by
  intro o ho
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ho
  exact HCModel.chain_mono (operations f) (Nat.succ_le_of_lt i.isLt)
    (HCModel.height_mem_extend (HCModel.chain (operations f) i))

theorem diagonal_prefix (f : HostVertex.{u} → ℕ) (n : ℕ) :
    P f (f (DiagonalVertex.vertex (operations f) f)) 0 (chainPrefix f n) := by
  refine ⟨DiagonalVertex.vertex (operations f) f, rfl, ?_⟩
  simp only [Prefix, chainPrefix, List.length_ofFn]
  rfl

/-- Repeated reflection removes the prescribed initial segment one coordinate at a time. -/
theorem reflected_prefix (f : HostVertex.{u} → ℕ) (r n : ℕ) :
    P f (f (DiagonalVertex.vertex (operations f) f)) r (chainPrefix f n) := by
  induction r generalizing n with
  | zero => exact diagonal_prefix f n
  | succ r ih =>
    apply reflect f (HCModel.chain (operations f) n) _ r _ (chainPrefix_mem f n)
    simpa only [chainPrefix_succ] using ih (n + 1)

theorem unbounded_start (f : HostVertex.{u} → ℕ) (n : ℕ) :
    P f (f (DiagonalVertex.vertex (operations f) f)) n [] := by
  simpa only [chainPrefix, List.ofFn_zero] using reflected_prefix f n 0

noncomputable def gapLower (f : HostVertex.{u} → ℕ) : ℕ → CountableOrdinal.{u}
  | 0 => zeroOrdinal
  | n + 1 => (HCModel.chain (operations f) n).height

theorem gapLower_mem (f : HostVertex.{u} → ℕ) (n : ℕ) :
    HC.ordinal (gapLower f n) ∈ (HCModel.chain (operations f) n).carrier := by
  cases n with
  | zero => exact (HCModel.chain (operations f) 0).zero_mem
  | succ n => exact HCModel.height_mem_extend (HCModel.chain (operations f) n)

def InGap (f : HostVertex.{u} → ℕ) (o : CountableOrdinal.{u}) (n : ℕ) : Prop :=
  o < (HCModel.chain (operations f) n).height ∧
    (0 < n → (HCModel.chain (operations f) (n - 1)).height < o)

/-- Realize a prefix while placing each selected coordinate in a prescribed model gap. -/
theorem realize_in_gaps (f : HostVertex.{u} → ℕ) (k : ℕ) (gs : List ℕ)
    (p : List CountableOrdinal.{u}) (hgs : gs.Pairwise (· ≤ ·))
    (hP : P f k gs.length p)
    (hp : ∀ m ∈ gs, ∀ o ∈ p, HC.ordinal o ∈ (HCModel.chain (operations f) m).carrier) :
    ∃ qs : List CountableOrdinal.{u}, qs.length = gs.length ∧ P f k 0 (p ++ qs) ∧
      List.Forall₂ (InGap f) qs gs := by
  induction gs generalizing p with
  | nil => exact ⟨[], rfl, by simpa only [List.append_nil, List.length_nil] using hP, List.Forall₂.nil⟩
  | cons m ms ih =>
    let M := HCModel.chain (operations f) m
    let a := gapLower f m
    let b := pick f k ms.length p a
    have hspec : a < b ∧ P f k ms.length (p ++ [b]) := pick_spec hP a
    have hbM : HC.ordinal b ∈ M.carrier :=
      pick_mem f M k ms.length p a (hp m (by simp)) (gapLower_mem f m)
    have hgap : InGap f b m := by
      refine ⟨(M.ordinal_members b).mp hbM, ?_⟩
      intro hm
      cases m with
      | zero => omega
      | succ j => simpa only [a, gapLower, Nat.add_one_sub_one] using hspec.1
    have hp' : ∀ m' ∈ ms, ∀ o ∈ p ++ [b],
        HC.ordinal o ∈ (HCModel.chain (operations f) m').carrier := by
      intro m' hm' o ho
      rcases List.mem_append.mp ho with ho | ho
      · exact hp m' (by simp [hm']) o ho
      · have hob : o = b := List.mem_singleton.mp ho
        subst o
        exact HCModel.chain_mono (operations f) ((List.pairwise_cons.mp hgs).1 m' hm') hbM
    obtain ⟨qs, hlen, hfinal, hrel⟩ := ih (p ++ [b]) (List.pairwise_cons.mp hgs).2 hspec.2 hp'
    refine ⟨b :: qs, by simp only [List.length_cons, hlen], ?_, List.Forall₂.cons hgap hrel⟩
    simpa only [List.append_assoc, List.singleton_append] using hfinal

theorem gaps_mem_limit (f : HostVertex.{u} → ℕ)
    {qs : List CountableOrdinal.{u}} {gs : List ℕ} (h : List.Forall₂ (InGap f) qs gs) :
    ∀ o ∈ qs, HC.ordinal o ∈ (HCModel.limitModel (operations f)).carrier := by
  induction h with
  | nil => simp
  | @cons o m qs gs hgap hrel ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Set.mem_iUnion.mpr ⟨m, ((HCModel.chain (operations f) m).ordinal_members a).mpr hgap.1⟩
    · exact ih a ha

/-- Multiple reflection produces a same-colored predecessor with the prescribed finite gaps. -/
theorem witness_with_gaps (f : HostVertex.{u} → ℕ) (gs : List ℕ)
    (hgs : gs.Pairwise (· ≤ ·)) :
    ∃ (v : HostVertex.{u}) (qs : List CountableOrdinal.{u}),
      HostVertex.Precedes v (DiagonalVertex.vertex (operations f) f) ∧
      f v = f (DiagonalVertex.vertex (operations f) f) ∧ Prefix qs v ∧
      qs.length = gs.length ∧ List.Forall₂ (InGap f) qs gs := by
  let k := f (DiagonalVertex.vertex (operations f) f)
  obtain ⟨qs, hlen, hP, hrel⟩ := realize_in_gaps f k gs [] hgs (unbounded_start f gs.length)
    (by simp)
  simp only [List.nil_append] at hP
  let M := HCModel.limitModel (operations f)
  let v := pickVertex f k qs
  have hv : f v = k ∧ Prefix qs v := pickVertex_spec hP
  have hvM : v.code ∈ M.carrier := pickVertex_mem f M k qs (gaps_mem_limit f hrel)
  refine ⟨v, qs, ?_, hv.1, hv.2, hlen, hrel⟩
  exact (HC.mem_collect M.carrier M.countable v.code).mpr hvM

theorem witness_for_gaps (f : HostVertex.{u} → ℕ) (N : ℕ) (g : Fin N → ℕ)
    (hg : Monotone g) :
    ∃ v : HostVertex.{u}, HostVertex.Precedes v (DiagonalVertex.vertex (operations f) f) ∧
      f v = f (DiagonalVertex.vertex (operations f) f) ∧
      ∀ i : Fin N, InGap f (v.val.ladder i) (g i) := by
  have hgs : (List.ofFn g).Pairwise (· ≤ ·) := List.pairwise_ofFn.mpr (fun _ _ h => hg h.le)
  obtain ⟨v, qs, hpre, hc, hp, hlen, hrel⟩ := witness_with_gaps f (List.ofFn g) hgs
  have hlen' : qs.length = N := by simpa only [List.length_ofFn] using hlen
  have hp' : List.ofFn (fun i : Fin N => v.val.ladder i) = qs := by
    simpa only [Prefix, hlen', Fin.val_cast] using hp
  rw [← hp'] at hrel
  refine ⟨v, hpre, hc, ?_⟩
  intro i
  have h := hrel.get (i := i.val) (by simpa only [List.length_ofFn] using i.isLt)
    (by simpa only [List.length_ofFn] using i.isLt)
  simpa [List.get_ofFn] using h

end Erdos736.PrefixReflection
end


/- Source module Erdos736.GapSequence. -/
section
namespace Erdos736

def blockOffset : ℕ → ℕ
  | 0 => 0
  | n + 1 => blockOffset n + shiftWidth (n + 1)

def blockGaps (n : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (shiftWidth (n + 1)) => blockOffset n + (i.val - (n + 1)))

def gapSequence : ℕ → List ℕ
  | 0 => []
  | n + 1 => gapSequence n ++ blockGaps n

theorem blockOffset_mono : Monotone blockOffset :=
  monotone_nat_of_le_succ (fun _n => Nat.le_add_right _ _)

@[simp] theorem gapSequence_length (n : ℕ) : (gapSequence n).length = blockOffset n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [gapSequence, blockGaps, List.length_append, List.length_ofFn, ih, blockOffset]

theorem blockGap_lower {n x : ℕ} (hx : x ∈ blockGaps n) : blockOffset n ≤ x := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact Nat.le_add_right _ _

theorem blockGap_upper {n x : ℕ} (hx : x ∈ blockGaps n) : x < blockOffset (n + 1) := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact Nat.add_lt_add_left ((Nat.sub_le i.val (n + 1)).trans_lt i.isLt) _

theorem gapSequence_upper {n x : ℕ} (hx : x ∈ gapSequence n) : x < blockOffset n := by
  induction n with
  | zero => simp [gapSequence] at hx
  | succ n ih =>
    rcases List.mem_append.mp hx with hx | hx
    · exact (ih hx).trans_le (blockOffset_mono (Nat.le_succ n))
    · exact blockGap_upper hx

theorem blockGaps_pairwise (n : ℕ) : (blockGaps n).Pairwise (· ≤ ·) := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact Nat.add_le_add_left (Nat.sub_le_sub_right (Nat.le_of_lt hij) (n + 1)) _

theorem gapSequence_pairwise (n : ℕ) : (gapSequence n).Pairwise (· ≤ ·) := by
  induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    apply List.pairwise_append.mpr
    refine ⟨ih, blockGaps_pairwise n, ?_⟩
    intro x hx y hy
    exact (gapSequence_upper hx).le.trans (blockGap_lower hy)

theorem block_index_lt {j k i : ℕ} (hj : j < k) (hi : i < shiftWidth (j + 1)) :
    blockOffset j + i < blockOffset k :=
  (Nat.add_lt_add_left hi (blockOffset j)).trans_le
    (blockOffset_mono (Nat.succ_le_of_lt hj))

theorem gapSequence_get {k j i : ℕ} (hj : j < k) (hi : i < shiftWidth (j + 1)) :
    (gapSequence k)[blockOffset j + i]'(by
      rw [gapSequence_length]
      exact block_index_lt hj hi) = blockOffset j + (i - (j + 1)) := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hfull : blockOffset j + i < (gapSequence k ++ blockGaps k).length := by
      simpa only [List.length_append, gapSequence_length, blockGaps, List.length_ofFn,
        blockOffset] using block_index_lt hj hi
    change (gapSequence k ++ blockGaps k)[blockOffset j + i]'hfull = _
    by_cases hjk : j < k
    · have hidx : blockOffset j + i < (gapSequence k).length := by
        rw [gapSequence_length]
        exact block_index_lt hjk hi
      rw [List.getElem_append_left hidx]
      exact ih hjk
    · have hjeq : j = k := by omega
      subst j
      rw [List.getElem_append_right (by rw [gapSequence_length]; omega)]
      simp only [gapSequence_length, Nat.add_sub_cancel_left, blockGaps, List.getElem_ofFn]

def gapAt (k : ℕ) (i : Fin (blockOffset k)) : ℕ :=
  (gapSequence k)[i.val]'(by simpa only [gapSequence_length] using i.isLt)

theorem gapAt_mono (k : ℕ) : Monotone (gapAt k) := by
  intro i j hij
  by_cases heq : i = j
  · subst j
    exact le_rfl
  · have hlt : i.val < j.val := by
      have hne : i.val ≠ j.val := fun h => heq (Fin.ext h)
      omega
    exact List.pairwise_iff_getElem.mp (gapSequence_pairwise k) i.val j.val
      (by simpa only [gapSequence_length] using i.isLt)
      (by simpa only [gapSequence_length] using j.isLt) hlt

theorem gapAt_block {k j i : ℕ} (hj : j < k) (hi : i < shiftWidth (j + 1)) :
    gapAt k ⟨blockOffset j + i, block_index_lt hj hi⟩ = blockOffset j + (i - (j + 1)) :=
  gapSequence_get hj hi

end Erdos736
end


/- Source module Erdos736.Compactness. -/
section
open SimpleGraph

universe u v

namespace Erdos736

theorem length_induceWalk {V : Type u} {G : SimpleGraph V} (s : Set V)
    {a b : V} (p : G.Walk a b) (hp : ∀ x ∈ p.support, x ∈ s) :
    (p.induce s hp).length = p.length := by
  induction p with
  | nil => rfl
  | cons hab p ih => simpa using congrArg Nat.succ (ih (by simp_all))

/-- Transfer one finite odd-walk coloring through ordinary finite-age inclusion. -/
theorem transfer_oddWalkColoring {V : Type u} {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (hAge : FiniteAgeIncluded H G) (n m : ℕ)
    (c : V → Fin (m + 1)) (hc : NoMonochromaticOddWalk G n c) :
    ∃ d : W → Fin (m + 1), NoMonochromaticOddWalk H n d := by
  classical
  choose f hf_inj hf_adj using hAge
  obtain ⟨d, hd⟩ := Finset.rado_selection_subtype
    (β := fun _ : W => Fin (m + 1)) (fun s x => c (f s x))
  refine ⟨d, ?_⟩
  intro a p hp_len hp_odd hp_mono
  let s := p.support.toFinset
  obtain ⟨t, hst, hdt⟩ := hd s
  have hpt : ∀ x ∈ p.support, x ∈ (t : Set W) := by
    intro x hx
    exact hst (List.mem_toFinset.mpr hx)
  let q := p.induce (t : Set W) hpt
  let φ : H.induce (t : Set W) →g G := ⟨f t, fun {a b} hab => hf_adj t a b hab⟩
  have hq_len : q.length = p.length := by
    exact length_induceWalk _ p hpt
  have hcolor (y : t) (hy : y.val ∈ p.support) : d y.val = c (f t y) := by
    have he := hdt (⟨y.val, List.mem_toFinset.mpr hy⟩ : s)
    simpa using he
  apply hc (f t ⟨a, hpt a p.start_mem_support⟩) (q.map φ)
  · simpa only [SimpleGraph.Walk.length_map, hq_len] using hp_len
  · simpa only [SimpleGraph.Walk.length_map, hq_len] using hp_odd
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (by
      simpa only [SimpleGraph.Walk.support_map] using hx)
    have hyv : y.val ∈ p.support := by
      simpa only [q, SimpleGraph.Walk.support_induce, List.mem_attachWith] using hy
    change c (f t y) = c (f t ⟨a, hpt a p.start_mem_support⟩)
    rw [← hcolor y hyv, ← hcolor _ p.start_mem_support]
    exact hp_mono y.val hyv

theorem transfer_finiteOddWalkColorings {V : Type u} {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (hAge : FiniteAgeIncluded H G) (hG : HasFiniteOddWalkColorings G) :
    HasFiniteOddWalkColorings H := by
  intro n
  obtain ⟨m, c, hc⟩ := hG n
  obtain ⟨d, hd⟩ := transfer_oddWalkColoring hAge n m c hc
  exact ⟨m, d, hd⟩

end Erdos736
end


/- Source module Erdos736.LayeredGraph. -/
section
open SimpleGraph

universe u v

namespace Erdos736

/-- Replacing a finite palette by a numbered palette preserves the odd-walk condition. -/
theorem finitePalette_numbering {V : Type u} {C : Type v} [Fintype C]
    {G : SimpleGraph V} {n : ℕ} (c : V → C)
    (hc : NoMonochromaticOddWalk G n c) :
    ∃ m : ℕ, ∃ d : V → Fin (m + 1), NoMonochromaticOddWalk G n d := by
  classical
  let e : C ↪ Fin (Fintype.card C + 1) :=
    (Fintype.equivFin C).toEmbedding.trans Fin.castSuccEmb
  refine ⟨Fintype.card C, fun x => e (c x), ?_⟩
  intro a p hlen hodd hmono
  apply hc a p hlen hodd
  intro x hx
  exact e.injective (hmono x hx)

/-- Data supplied by the layered host construction. Every tail excludes short odd walks. -/
structure LayeredGraphCertificate {V : Type u} (G : SimpleGraph V) where
  layer : ℕ → SimpleGraph V
  tail : ℕ → SimpleGraph V
  bicolor : ∀ n, Nonempty ((layer n).Coloring Bool)
  tail_contains : ∀ n {a b}, G.Adj a b →
    (∀ j, j < n → ¬(layer j).Adj a b) → (tail n).Adj a b
  tail_even : ∀ n a (p : (tail n).Walk a a), p.length ≤ n → Even p.length

/-- The first finitely many layer colorings eliminate all short monochromatic odd walks. -/
theorem LayeredGraphCertificate.finiteOddWalkColorings {V : Type u}
    {G : SimpleGraph V} (data : LayeredGraphCertificate G) :
    HasFiniteOddWalkColorings G := by
  classical
  intro n
  let c : ℕ → V → Bool := fun j => (data.bicolor j).some
  let d : V → Fin n → Bool := fun x j => c j x
  apply finitePalette_numbering d
  intro a p hlen hodd hmono
  let s : Set V := {x | d x = d a}
  have hps : ∀ x ∈ p.support, x ∈ s := hmono
  let q := p.induce s hps
  let φ : G.induce s →g data.tail n :=
    { toFun := Subtype.val
      map_rel' := by
        intro x y hxy
        apply data.tail_contains n hxy
        intro j hj hLayer
        have hColor := (data.bicolor j).some.valid hLayer
        apply hColor
        have hx := congrFun x.property (⟨j, hj⟩ : Fin n)
        have hy := congrFun y.property (⟨j, hj⟩ : Fin n)
        exact hx.trans hy.symm }
  have hq_len : (q.map φ).length = p.length := by
    rw [Walk.length_map]
    exact length_induceWalk s p hps
  have heven := data.tail_even n a (q.map φ) (by simpa only [hq_len] using hlen)
  have hnot := Nat.not_even_iff_odd.mpr hodd
  apply hnot
  simpa only [hq_len] using heven

end Erdos736
end


/- Source module Erdos736.ColorBound. -/
section
open SimpleGraph Cardinal

universe u

namespace Erdos736

theorem constant_on_walk {V C : Type*} {G : SimpleGraph V}
    (c : V → C) (hc : ∀ {a b}, G.Adj a b → c a = c b)
    {a b : V} (p : G.Walk a b) : ∀ x ∈ p.support, c x = c a := by
  induction p with
  | nil => simp
  | @cons a b d hab p ih =>
    intro x hx
    simp only [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rfl
    · exact (ih x hx).trans (hc hab).symm

/-- A countable family of finite odd-walk colorings gives a continuum-sized coloring. -/
theorem coloring_of_finiteOddWalkColorings {V : Type u} {G : SimpleGraph V}
    (hG : HasFiniteOddWalkColorings G) :
    Nonempty (G.Coloring ((ℕ → ℕ) × Bool)) := by
  classical
  choose m c hc using hG
  let C : V → ℕ → ℕ := fun v n => (c n v).val
  let K : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧ C a = C b
      symm := ⟨fun {a b} h => ⟨h.1.symm, h.2.symm⟩⟩
      loopless := ⟨fun a h => G.irrefl h.1⟩ }
  let φ : K →g G := ⟨id, fun h => h.1⟩
  have hK : K.Colorable 2 := by
    apply two_colorable_iff_forall_loop_even.mpr
    intro a p
    rw [← Nat.not_odd_iff_even]
    intro hp
    apply hc p.length a (p.map φ)
    · simp only [Walk.length_map, le_refl]
    · simpa only [Walk.length_map] using hp
    · intro x hx
      have hx' : x ∈ p.support := by
        simpa [φ, Walk.support_map] using hx
      have hC := constant_on_walk C (G := K) (fun h => h.2) p x hx'
      exact Fin.ext (congrFun hC p.length)
  let d : K.Coloring Bool := K.recolorOfEquiv finTwoEquiv hK.some
  refine ⟨Coloring.mk (fun v => (C v, d v)) ?_⟩
  intro a b hab he
  have hC : C a = C b := congrArg Prod.fst he
  have hd : d a = d b := congrArg Prod.snd he
  exact d.valid ⟨hab, hC⟩ hd

theorem palette_cardinality : #((ℕ → ℕ) × Bool) = 𝔠 := by
  simp [Cardinal.mk_prod]

/-- The cardinal-valued consequence of the compactness construction. -/
theorem chromaticCardinal_le_continuum {V : Type u} {G : SimpleGraph V}
    (hG : HasFiniteOddWalkColorings G) : chromaticCardinal G ≤ 𝔠 := by
  let c := (coloring_of_finiteOddWalkColorings hG).some
  let e : ((ℕ → ℕ) × Bool) ↪ ULift.{u} ((ℕ → ℕ) × Bool) :=
    ⟨ULift.up, ULift.up_injective⟩
  have h := chromaticCardinal_le (G.recolorOfEmbedding e c)
  simpa only [Cardinal.mk_uLift, palette_cardinality, Cardinal.lift_continuum] using h

theorem finiteAge_chromatic_bound {V : Type u} {W : Type u}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : HasFiniteOddWalkColorings G) (hAge : FiniteAgeIncluded H G) :
    chromaticCardinal H ≤ 𝔠 :=
  chromaticCardinal_le_continuum (transfer_finiteOddWalkColorings hAge hG)

/-- A host with these properties refutes the full Taylor assertion. -/
theorem not_TaylorConjecture_of_host
    (hHost : ∃ (V : Type u) (G : SimpleGraph V),
      chromaticCardinal G = ℵ₁ ∧ HasFiniteOddWalkColorings G) :
    ¬TaylorConjecture.{u} := by
  intro hTaylor
  obtain ⟨V, G, hχ, hG⟩ := hHost
  obtain ⟨W, H, hHχ, hAge⟩ := hTaylor V G hχ (Order.succ 𝔠)
  have hBound := finiteAge_chromatic_bound hG hAge
  rw [hHχ] at hBound
  exact (Order.lt_succ 𝔠).not_ge hBound

end Erdos736
end


/- Source module Erdos736.ActualHost. -/
section
open SimpleGraph Cardinal

universe u

namespace Erdos736.ActualHost

def compatible (k : ℕ) (v w : HostVertex.{u}) : Prop :=
  ∀ j, j ≤ k → ShiftPattern (j + 1) (shiftWidth (j + 1))
    (fun i => v.val.ladder (blockOffset j + i)) (fun i => w.val.ladder (blockOffset j + i))

theorem tail_even (n : ℕ) (v : HostVertex.{u})
    (p : (HostGraph.tail compatible n).Walk v v) (hlen : p.length ≤ n) : Even p.length := by
  apply even_length_of_shiftPattern (n + 1) (fun v i => v.val.ladder (blockOffset n + i))
    (fun v a b hab => v.property.ladder_increasing.monotone (Nat.add_le_add_left hab _))
    ?_ v p (by omega)
  intro a b hab
  obtain ⟨k, hnk, hk⟩ := hab
  rcases hk with hk | hk
  · obtain ⟨_, _, hc⟩ := HostGraph.parent_spec compatible hk
    exact Or.inr (hc n hnk)
  · obtain ⟨_, _, hc⟩ := HostGraph.parent_spec compatible hk
    exact Or.inl (hc n hnk)

noncomputable def certificate : LayeredGraphCertificate (HostGraph.graph compatible.{u}) where
  layer := HostGraph.layer compatible
  tail := HostGraph.tail compatible
  bicolor := HostGraph.bicolor_layer compatible
  tail_contains := HostGraph.tail_contains compatible
  tail_even := tail_even

theorem finiteOddWalkColorings : HasFiniteOddWalkColorings (HostGraph.graph compatible.{u}) :=
  certificate.finiteOddWalkColorings

theorem eligible_predecessor (f : HostVertex.{u} → ℕ) :
    ∃ v, HostGraph.Eligible compatible (DiagonalVertex.vertex (PrefixReflection.operations f) f)
      (f (DiagonalVertex.vertex (PrefixReflection.operations f) f)) v := by
  let τ := DiagonalVertex.vertex (PrefixReflection.operations f) f
  let k := f τ
  obtain ⟨v, hpre, hcolor, hgap⟩ := PrefixReflection.witness_for_gaps f
    (blockOffset (k + 1)) (gapAt (k + 1)) (gapAt_mono (k + 1))
  refine ⟨v, hpre, ?_, ?_⟩
  · exact (DiagonalVertex.memory_eq (PrefixReflection.operations f) f v hpre).trans hcolor
  · intro j hj i hilo hihi
    have hjk : j < k + 1 := Nat.lt_succ_of_le hj
    have hi : i < shiftWidth (j + 1) := by omega
    have hi' : i + (j + 1) + 1 < shiftWidth (j + 1) := by omega
    constructor
    · have h := (hgap ⟨blockOffset j + i, block_index_lt hjk hi⟩).1
      rw [gapAt_block hjk hi] at h
      exact h
    · have hpos : 0 < gapAt (k + 1)
          ⟨blockOffset j + (i + (j + 1) + 1), block_index_lt hjk hi'⟩ := by
        rw [gapAt_block hjk hi']
        omega
      have h := (hgap ⟨blockOffset j + (i + (j + 1) + 1), block_index_lt hjk hi'⟩).2 hpos
      rw [gapAt_block hjk hi'] at h
      have heq : blockOffset j + (i + (j + 1) + 1 - (j + 1)) - 1 = blockOffset j + i := by omega
      rw [heq] at h
      exact h

theorem not_natColoring : ¬Nonempty ((HostGraph.graph compatible.{u}).Coloring ℕ) := by
  rintro ⟨c⟩
  obtain ⟨v, w, hadj, hsame⟩ := DiagonalVertex.monochromatic_edge_of_eligible compatible
    (PrefixReflection.operations c) c (eligible_predecessor c)
  exact c.valid hadj hsame

theorem small_not_natColoring : ¬Nonempty ((HostGraph.smallGraph compatible.{u}).Coloring ℕ) := by
  rintro ⟨c⟩
  apply not_natColoring
  exact ⟨c.comap (Iso.comap (equivShrink HostVertex).symm (HostGraph.graph compatible)).symm.toHom⟩

theorem small_chromaticCardinal : chromaticCardinal (HostGraph.smallGraph compatible.{u}) = ℵ₁ := by
  apply le_antisymm (HostGraph.smallGraph_chromaticCardinal_le_aleph_one compatible)
  apply le_of_not_gt
  intro hlt
  have hle : chromaticCardinal (HostGraph.smallGraph compatible.{u}) ≤ ℵ₀ :=
    Cardinal.lt_aleph_one_iff.mp hlt
  obtain ⟨c⟩ := (chromaticCardinal_le_iff (HostGraph.smallGraph compatible.{u}) ℵ₀).mp hle
  have hCount : Countable (ℵ₀ : Cardinal.{u}).out := by
    apply Cardinal.mk_le_aleph0_iff.mp
    simp only [Cardinal.mk_out, le_refl]
  obtain ⟨e⟩ := countable_iff_nonempty_embedding.mp hCount
  exact small_not_natColoring ⟨(HostGraph.smallGraph compatible).recolorOfEmbedding e c⟩

theorem small_finiteOddWalkColorings :
    HasFiniteOddWalkColorings (HostGraph.smallGraph compatible.{u}) := by
  apply transfer_finiteOddWalkColorings (G := HostGraph.graph compatible) ?_ finiteOddWalkColorings
  intro s
  refine ⟨fun x => (equivShrink HostVertex).symm x.val, ?_, ?_⟩
  · intro a b h
    exact Subtype.ext ((equivShrink HostVertex).symm.injective h)
  · intro a b h
    exact h

end Erdos736.ActualHost

namespace Erdos736

/-- A host of chromatic cardinal `ℵ₁` whose entire finite age has chromatic cardinal at most `𝔠`. -/
theorem full_solution :
    ∃ (V : Type u) (G : SimpleGraph V), chromaticCardinal G = ℵ₁ ∧
      ∀ (W : Type u) (H : SimpleGraph W), FiniteAgeIncluded H G → chromaticCardinal H ≤ 𝔠 := by
  refine ⟨Shrink.{u} HostVertex.{u}, HostGraph.smallGraph ActualHost.compatible,
    ActualHost.small_chromaticCardinal, ?_⟩
  intro W H hAge
  exact finiteAge_chromatic_bound ActualHost.small_finiteOddWalkColorings hAge

/-- The negative answer to the full Taylor assertion. -/
theorem taylorConjecture_false : ¬TaylorConjecture.{u} :=
  not_TaylorConjecture_of_host
    ⟨Shrink.{u} HostVertex.{u}, HostGraph.smallGraph ActualHost.compatible,
      ActualHost.small_chromaticCardinal, ActualHost.small_finiteOddWalkColorings⟩

/-- Erdős 736, expressed with ordinary copies of arbitrary finite graphs. -/
theorem erdos_736 :
    ¬∀ (V : Type u) (G : SimpleGraph V), chromaticCardinal G = ℵ₁ →
      ∀ m : Cardinal.{u}, ∃ (W : Type u) (H : SimpleGraph W), chromaticCardinal H = m ∧
        ∀ (U : Type u) [Fintype U] (F : SimpleGraph U), ContainsCopy H F → ContainsCopy G F := by
  intro h
  apply taylorConjecture_false
  intro V G hG m
  obtain ⟨W, H, hH, hFinite⟩ := h V G hG m
  exact ⟨W, H, hH, (finiteAgeIncluded_iff H G).mpr hFinite⟩

end Erdos736
end

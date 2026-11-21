import Atoms.Molecule.Construction.Join
import Atoms.Molecule.MoleculeShape.Basic

open Order

namespace Atoms.Molecule

open OGP

namespace MoleculeShape

def joinRDC (U : MoleculeShape) (Q : OGP.{0}) (hQ : IsMolecule Q) : RDCpx.{0} :=
  ⟨⟨join U.ogp Q, isRDC_of_isMolecule (isMolecule_join _ _ U.isMolecule hQ)⟩⟩

instance (U : MoleculeShape) (Q : OGP.{0}) (hQ : IsMolecule Q) [FinEnum Q] :
    FinEnum (joinRDC U Q hQ).obj.toOGP :=
  inferInstanceAs (FinEnum (join U.ogp Q))

instance (U : MoleculeShape) (Q : OGP.{0}) (hQ : IsMolecule Q) [DecidableLE Q] :
    DecidableLE (joinRDC U Q hQ).obj.toOGP :=
  inferInstanceAs (DecidableLE (join U.ogp Q))

private def MemAug {P : OGP.{0}} (A : LowerSet P) (o : WithBot P) : Prop :=
  ∀ a : P, o = (a : WithBot P) → a ∈ A

private theorem MemAug.mono {P : OGP.{0}} {A A' : LowerSet P} (h : A ≤ A') {o : WithBot P}
    (ho : MemAug A o) : MemAug A' o :=
  fun a ha => h (ho a ha)

private theorem MemAug.of_le {P : OGP.{0}} {A : LowerSet P} {o o' : WithBot P} (h : o' ≤ o)
    (ho : MemAug A o) : MemAug A o' := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := WithBot.coe_le_iff.1 (ha ▸ h)
  exact A.lower hab (ho b hb)

private theorem memAug_sup {P : OGP.{0}} {A A' : LowerSet P} {o : WithBot P} :
    MemAug (A ⊔ A') o ↔ MemAug A o ∨ MemAug A' o := by
  induction o using WithBot.recBotCoe with
  | bot => exact ⟨fun _ => Or.inl fun _ h => absurd h WithBot.bot_ne_coe,
      fun _ _ h => absurd h WithBot.bot_ne_coe⟩
  | coe c =>
    simp only [MemAug, WithBot.coe_inj, forall_eq', LowerSet.mem_sup_iff]

private theorem memAug_inf {P : OGP.{0}} {A A' : LowerSet P} {o : WithBot P} :
    MemAug (A ⊓ A') o ↔ MemAug A o ∧ MemAug A' o :=
  ⟨fun h => ⟨fun a ha => (h a ha).1, fun a ha => (h a ha).2⟩, fun h a ha => ⟨h.1 a ha, h.2 a ha⟩⟩

def joinPair (U : MoleculeShape) {Q : OGP.{0}} (hQ : IsMolecule Q) (A : LowerSet U.ogp)
    (B : LowerSet Q) : LowerSet (joinRDC U Q hQ).obj.toOGP where
  carrier := {p | (∀ a : U.ogp, p.1.1 = (a : WithBot _) → a ∈ A) ∧
    ∀ b : Q, p.1.2 = (b : WithBot _) → b ∈ B}
  lower' _ _ hqp hp :=
    ⟨MemAug.of_le (join_le_iff.1 hqp).1 hp.1, MemAug.of_le (join_le_iff.1 hqp).2 hp.2⟩

def leibnizJoinSubset (U : MoleculeShape) {Q : OGP.{0}} (hQ : IsMolecule Q)
    (A A' : LowerSet U.ogp) (B B' : LowerSet Q) : LowerSet (joinRDC U Q hQ).obj.toOGP :=
  joinPair U hQ A' B' ⊓ (joinPair U hQ A' B ⊔ joinPair U hQ A B')

variable (U : MoleculeShape) {Q : OGP.{0}} (hQ : IsMolecule Q)

theorem mem_joinPair {A : LowerSet U.ogp} {B : LowerSet Q} {p : (joinRDC U Q hQ).obj.toOGP} :
    p ∈ joinPair U hQ A B ↔ (∀ a : U.ogp, p.1.1 = (a : WithBot _) → a ∈ A) ∧
      ∀ b : Q, p.1.2 = (b : WithBot _) → b ∈ B :=
  Iff.rfl

private theorem mem_joinPair_iff {A : LowerSet U.ogp} {B : LowerSet Q}
    {p : (joinRDC U Q hQ).obj.toOGP} :
    p ∈ joinPair U hQ A B ↔ MemAug A p.1.1 ∧ MemAug B p.1.2 :=
  Iff.rfl

theorem mem_leibnizJoinSubset {A A' : LowerSet U.ogp} {B B' : LowerSet Q} (hA : A ≤ A')
    (hB : B ≤ B') {p : (joinRDC U Q hQ).obj.toOGP} :
    p ∈ leibnizJoinSubset U hQ A A' B B' ↔ p ∈ joinPair U hQ A' B' ∧
      ((∀ b : Q, p.1.2 = (b : WithBot _) → b ∈ B) ∨
        ∀ a : U.ogp, p.1.1 = (a : WithBot _) → a ∈ A) := by
  have h₁ := @MemAug.mono _ _ _ hA p.1.1
  have h₂ := @MemAug.mono _ _ _ hB p.1.2
  simp only [leibnizJoinSubset, LowerSet.mem_inf_iff, LowerSet.mem_sup_iff, mem_joinPair_iff]
  exact ⟨fun h => ⟨h.1, by tauto⟩, fun h => ⟨h.1, by tauto⟩⟩

theorem joinPair_mono {A A' : LowerSet U.ogp} {B B' : LowerSet Q} (hA : A ≤ A') (hB : B ≤ B') :
    joinPair U hQ A B ≤ joinPair U hQ A' B' :=
  fun _ hp => ⟨MemAug.mono hA hp.1, MemAug.mono hB hp.2⟩

theorem joinPair_sup_left (A A' : LowerSet U.ogp) (B : LowerSet Q) :
    joinPair U hQ (A ⊔ A') B = joinPair U hQ A B ⊔ joinPair U hQ A' B := by
  refine SetLike.ext fun p => ?_
  simp only [LowerSet.mem_sup_iff, mem_joinPair_iff, memAug_sup]
  tauto

theorem joinPair_sup_right (A : LowerSet U.ogp) (B B' : LowerSet Q) :
    joinPair U hQ A (B ⊔ B') = joinPair U hQ A B ⊔ joinPair U hQ A B' := by
  refine SetLike.ext fun p => ?_
  simp only [LowerSet.mem_sup_iff, mem_joinPair_iff, memAug_sup]
  tauto

theorem joinPair_inf (A A' : LowerSet U.ogp) (B B' : LowerSet Q) :
    joinPair U hQ (A ⊓ A') (B ⊓ B') = joinPair U hQ A B ⊓ joinPair U hQ A' B' := by
  refine SetLike.ext fun p => ?_
  simp only [LowerSet.mem_inf_iff, mem_joinPair_iff, memAug_inf]
  tauto

theorem leibnizJoinSubset_mono {A₁ A₂ A₁' A₂' : LowerSet U.ogp} {B₁ B₂ B₁' B₂' : LowerSet Q}
    (hA : A₁ ≤ A₂) (hA' : A₁' ≤ A₂') (hB : B₁ ≤ B₂) (hB' : B₁' ≤ B₂') :
    leibnizJoinSubset U hQ A₁ A₁' B₁ B₁' ≤ leibnizJoinSubset U hQ A₂ A₂' B₂ B₂' :=
  inf_le_inf (joinPair_mono U hQ hA' hB')
    (sup_le_sup (joinPair_mono U hQ hA' hB) (joinPair_mono U hQ hA hB'))

theorem joinPair_le_leibnizJoinSubset {B B' : LowerSet Q} (A A' : LowerSet U.ogp) (hB : B ≤ B') :
    joinPair U hQ A' B ≤ leibnizJoinSubset U hQ A A' B B' :=
  le_inf (joinPair_mono U hQ le_rfl hB) le_sup_left

theorem leibnizJoinSubset_self_left (A : LowerSet U.ogp) (B B' : LowerSet Q) :
    leibnizJoinSubset U hQ A A B B' = joinPair U hQ A B' :=
  le_antisymm inf_le_left (le_inf le_rfl le_sup_right)

theorem leibnizJoinSubset_self_right (A A' : LowerSet U.ogp) (B : LowerSet Q) :
    leibnizJoinSubset U hQ A A' B B = joinPair U hQ A' B :=
  inf_sup_self

theorem leibnizJoinSubset_sup_left {A A' C C' : LowerSet U.ogp} (hA : A ≤ A') (hC : C ≤ C')
    (B B' : LowerSet Q) :
    leibnizJoinSubset U hQ A A' B B' ⊔ leibnizJoinSubset U hQ C C' B B' =
      leibnizJoinSubset U hQ (A ⊔ C) (A' ⊔ C') B B' := by
  refine SetLike.ext fun p => ?_
  have h₁ := @MemAug.mono _ _ _ hA p.1.1
  have h₂ := @MemAug.mono _ _ _ hC p.1.1
  simp only [leibnizJoinSubset, LowerSet.mem_sup_iff, LowerSet.mem_inf_iff, mem_joinPair_iff,
    memAug_sup]
  tauto

theorem leibnizJoinSubset_inf_left {A A' C C' : LowerSet U.ogp} (hA : A ≤ A') (hC : C ≤ C')
    (B B' : LowerSet Q) :
    leibnizJoinSubset U hQ A A' B B' ⊓ leibnizJoinSubset U hQ C C' B B' =
      leibnizJoinSubset U hQ (A ⊓ C) (A' ⊓ C') B B' := by
  refine SetLike.ext fun p => ?_
  have h₁ := @MemAug.mono _ _ _ hA p.1.1
  have h₂ := @MemAug.mono _ _ _ hC p.1.1
  simp only [leibnizJoinSubset, LowerSet.mem_sup_iff, LowerSet.mem_inf_iff, mem_joinPair_iff,
    memAug_inf]
  tauto

theorem joinPair_inf_leibnizJoinSubset_left {A₁ A₂ A₃ : LowerSet U.ogp} (h₁₂ : A₁ ≤ A₂)
    (h₂₃ : A₂ ≤ A₃) (B B' : LowerSet Q) :
    joinPair U hQ A₂ B' ⊓ leibnizJoinSubset U hQ A₁ A₃ B B' =
      leibnizJoinSubset U hQ A₁ A₂ B B' := by
  refine SetLike.ext fun p => ?_
  have h₁ := @MemAug.mono _ _ _ h₁₂ p.1.1
  have h₂ := @MemAug.mono _ _ _ h₂₃ p.1.1
  simp only [leibnizJoinSubset, LowerSet.mem_sup_iff, LowerSet.mem_inf_iff, mem_joinPair_iff]
  tauto

theorem leibnizJoinSubset_sup_joinPair_left {A₁ A₂ A₃ : LowerSet U.ogp} (h₁₂ : A₁ ≤ A₂)
    (h₂₃ : A₂ ≤ A₃) (B B' : LowerSet Q) :
    leibnizJoinSubset U hQ A₁ A₃ B B' ⊔ joinPair U hQ A₂ B' =
      leibnizJoinSubset U hQ A₂ A₃ B B' := by
  refine SetLike.ext fun p => ?_
  have h₁ := @MemAug.mono _ _ _ h₁₂ p.1.1
  have h₂ := @MemAug.mono _ _ _ h₂₃ p.1.1
  simp only [leibnizJoinSubset, LowerSet.mem_sup_iff, LowerSet.mem_inf_iff, mem_joinPair_iff]
  tauto

theorem joinPair_inf_leibnizJoinSubset_right {A A' : LowerSet U.ogp} (hA : A ≤ A')
    {B₁ B₂ B₃ : LowerSet Q} (h₁₂ : B₁ ≤ B₂) (h₂₃ : B₂ ≤ B₃) :
    joinPair U hQ A' B₂ ⊓ leibnizJoinSubset U hQ A A' B₁ B₃ =
      leibnizJoinSubset U hQ A A' B₁ B₂ := by
  refine SetLike.ext fun p => ?_
  have h₀ := @MemAug.mono _ _ _ hA p.1.1
  have h₁ := @MemAug.mono _ _ _ h₁₂ p.1.2
  have h₂ := @MemAug.mono _ _ _ h₂₃ p.1.2
  simp only [leibnizJoinSubset, LowerSet.mem_sup_iff, LowerSet.mem_inf_iff, mem_joinPair_iff]
  tauto

theorem leibnizJoinSubset_sup_joinPair_right {A A' : LowerSet U.ogp} (hA : A ≤ A')
    {B₁ B₂ B₃ : LowerSet Q} (h₁₂ : B₁ ≤ B₂) (h₂₃ : B₂ ≤ B₃) :
    leibnizJoinSubset U hQ A A' B₁ B₃ ⊔ joinPair U hQ A' B₂ =
      leibnizJoinSubset U hQ A A' B₂ B₃ := by
  refine SetLike.ext fun p => ?_
  have h₀ := @MemAug.mono _ _ _ hA p.1.1
  have h₁ := @MemAug.mono _ _ _ h₁₂ p.1.2
  have h₂ := @MemAug.mono _ _ _ h₂₃ p.1.2
  simp only [leibnizJoinSubset, LowerSet.mem_sup_iff, LowerSet.mem_inf_iff, mem_joinPair_iff]
  tauto

theorem leibnizJoinSubset_sup_right_eq {A A' : LowerSet U.ogp} (hA : A ≤ A') (B C : LowerSet Q) :
    leibnizJoinSubset U hQ A A' B (B ⊔ C) =
      joinPair U hQ A' B ⊔ leibnizJoinSubset U hQ A A' (B ⊓ C) C := by
  refine SetLike.ext fun p => ?_
  have h₀ := @MemAug.mono _ _ _ hA p.1.1
  simp only [leibnizJoinSubset, LowerSet.mem_sup_iff, LowerSet.mem_inf_iff, mem_joinPair_iff,
    memAug_sup, memAug_inf]
  tauto

end MoleculeShape

end Atoms.Molecule

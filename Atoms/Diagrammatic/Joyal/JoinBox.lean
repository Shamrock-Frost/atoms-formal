import Atoms.Diagrammatic.Marked.Above
import Atoms.Diagrammatic.Marked.LeftProper
import Atoms.Diagrammatic.RealizationColimits
import Atoms.Molecule.Construction.JoinInclusion
import Atoms.Molecule.Construction.JoinSimplex
import Atoms.Molecule.Construction.LeibnizJoin

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

universe u

namespace Atoms.Diagrammatic

open Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape Order

def joinBox (U : MoleculeShape) (r : ℕ) (P Q : LowerSet U.ogp) :
    realize.{u}.obj (RDCpx.restrict (MoleculeShape.joinSimplexRDC U r)
        (MoleculeShape.joinBoxSubset U r P Q)) ⟶
      realize.obj (RDCpx.restrict (MoleculeShape.joinSimplexRDC U r)
        (MoleculeShape.joinSubset U r Q)) :=
  realize.map (RDCpx.inclusion _ inf_le_left)

def leibnizJoinBox (U : MoleculeShape) {Q : OGP.{0}} (hQ : IsMolecule Q)
    (A A' : LowerSet U.ogp) (B B' : LowerSet Q) :
    realize.{u}.obj (RDCpx.restrict (MoleculeShape.joinRDC U Q hQ)
        (MoleculeShape.leibnizJoinSubset U hQ A A' B B')) ⟶
      realize.obj (RDCpx.restrict (MoleculeShape.joinRDC U Q hQ)
        (MoleculeShape.joinPair U hQ A' B')) :=
  realize.map (RDCpx.inclusion _ inf_le_left)

section Ambient

variable (n : ℕ∞) (K : RDCpx.{0})

private def AcyclicIn {A A' : LowerSet K.obj.toOGP} (h : A ≤ A') : Prop :=
  markedExactCylinder.{u}.weakEquivalences (coinductiveGenerators n)
    ((MarkedDiagSet.markedAboveFunctor 1).map (realize.map (RDCpx.inclusion K h)))

variable {n K}

private theorem acyclicIn_congr {A A' B B' : LowerSet K.obj.toOGP} {h : A ≤ A'} {h' : B ≤ B'}
    (e : A = B) (e' : A' = B') : AcyclicIn.{u} n K h ↔ AcyclicIn.{u} n K h' := by
  subst e e'
  rfl

private theorem acyclicIn_of_eq {A A' : LowerSet K.obj.toOGP} {h : A ≤ A'} (e : A = A') :
    AcyclicIn.{u} n K h := by
  subst e
  refine markedExactCylinder.{u}.isomorphisms_le_weakEquivalences _ _ ?_
  have : RDCpx.inclusion K h = 𝟙 _ := by
    ext
    rfl
  rw [this, realize.map_id, CategoryTheory.Functor.map_id]
  exact isomorphisms.infer_property _

private theorem markedAbove_realize_map_comp {S T R : LowerSet K.obj.toOGP} (hST : S ≤ T)
    (hTR : T ≤ R) :
    (MarkedDiagSet.markedAboveFunctor.{u} 1).map (realize.map (RDCpx.inclusion K hST)) ≫
      (MarkedDiagSet.markedAboveFunctor 1).map (realize.map (RDCpx.inclusion K hTR)) =
    (MarkedDiagSet.markedAboveFunctor 1).map (realize.map (RDCpx.inclusion K (hST.trans hTR))) := by
  rw [← Functor.map_comp, realize_map_restrictInclOfSubset_comp]

private theorem AcyclicIn.trans {A A' A'' : LowerSet K.obj.toOGP} {h : A ≤ A'} {h' : A' ≤ A''}
    (h₁ : AcyclicIn.{u} n K h) (h₂ : AcyclicIn.{u} n K h') : AcyclicIn.{u} n K (h.trans h') := by
  have h₃ := MorphismProperty.comp_mem _ _ _ h₁ h₂
  rwa [markedAbove_realize_map_comp] at h₃

private theorem mono_markedAbove_realize_map {S T : LowerSet K.obj.toOGP} (hST : S ≤ T) :
    Mono ((MarkedDiagSet.markedAboveFunctor.{u} 1).map (realize.map (RDCpx.inclusion K hST))) :=
  have := mono_realize_map (RDCpx.inclusion K hST)
    fun a b hab => Subtype.ext (by have := congrArg Subtype.val hab; exact this)
  MarkedDiagSet.mono_markedAboveFunctor_map 1 _

private theorem acyclicIn_sup {A A' B B' : LowerSet K.obj.toOGP} (h : A ≤ A') (h' : B ≤ B')
    (h₀ : AcyclicIn.{u} n K (inf_le_inf h h')) (h₁ : AcyclicIn.{u} n K h)
    (h₂ : AcyclicIn.{u} n K h') :
    AcyclicIn.{u} n K (sup_le_sup h h') := by
  have := mono_markedAbove_realize_map (K := K) (inf_le_left : A ⊓ B ≤ A)
  have := mono_markedAbove_realize_map (K := K) (inf_le_left : A' ⊓ B' ≤ A')
  refine markedExactCylinder.{u}.weakEquivalences_of_isPushout_of_mono
    (coinductiveGenerators_le_monomorphisms n)
    (MarkedDiagSet.isPushout_markedAboveFunctor_map 1
      (isPushout_realize_restrictInclOfSubset K A B))
    (MarkedDiagSet.isPushout_markedAboveFunctor_map 1
      (isPushout_realize_restrictInclOfSubset K A' B')) _ _ _ _ ?_ ?_ ?_ ?_ h₀ h₁ h₂ <;>
  · rw [markedAbove_realize_map_comp, markedAbove_realize_map_comp]

private theorem acyclicIn_sup_right {A A' R : LowerSet K.obj.toOGP} (h : A ≤ A')
    (hAR : A' ⊓ R ≤ A) (h₁ : AcyclicIn.{u} n K h) :
    AcyclicIn.{u} n K (sup_le_sup h (le_refl R)) :=
  acyclicIn_sup h le_rfl
    (acyclicIn_of_eq (le_antisymm (inf_le_inf h le_rfl) (le_inf hAR inf_le_right))) h₁
    (acyclicIn_of_eq rfl)

private theorem acyclicIn_horn [∀ x : K.obj.toOGP, FinEnum (K.obj.toOGP.restrict (.Iic x))]
    {w e : K.obj.toOGP} (hew : e ⋖ w)
    (hK : ∀ α, K.obj.toOGP.boundary (LowerSet.Iic e) 0 α =
      K.obj.toOGP.boundary (LowerSet.Iic w) 0 α)
    {S : LowerSet K.obj.toOGP} (hS : ∀ p, p ∈ S ↔ p ≤ w ∧ p ≠ w ∧ p ≠ e)
    (hSw : S ≤ LowerSet.Iic w) : AcyclicIn.{u} n K hSw := by
  classical
  let T := principalAtomRDC K w
  let ι := principalInclusionOGP K w
  have hιtop : ι T.top = w := principalInclusionRDC_top K w
  let x' : T.ogp := (principalAtomIsoRDC K w).hom ⟨e, LowerSet.mem_Iic_iff.2 hew.le⟩
  have hιx : ι x' = e := principalInclusionRDC_apply_principalAtomIsoRDC K w _
  have hdew : grade ℕ e + 1 = grade ℕ w := Nat.covBy_iff_add_one_eq.1 (hew.grade ℕ)
  have h₁ : grade ℕ (ι T.top) = grade ℕ T.top := (isMorphism ι).grade_eq T.top
  have h₂ : grade ℕ (ι x') = grade ℕ x' := (isMorphism ι).grade_eq x'
  rw [hιtop] at h₁
  rw [hιx] at h₂
  have hxtop : x' ⋖ T.top :=
    GradeOrder.covBy_of_le_of_grade_eq_add_one (T.le_top x') (by omega)
  let h := atomicHornDataOfCovBy T x' hxtop
  have hS' : ∀ a, a ∈ hornSubset h.toHornData ↔
      ConcreteCategory.hom (principalInclusionRDC K w).hom a ∈ S := by
    intro a
    rw [hS, mem_hornSet_closure_singleton_iff h.toHornData (x := x') rfl]
    refine ⟨fun ⟨ht, hx⟩ => ⟨LowerSet.mem_Iic_iff.1 (principalInclusionRDC_mem_closure K w a),
      fun hw => ht ?_, fun he => hx ?_⟩, fun ⟨_, hw, he⟩ => ⟨fun ht => hw ?_, fun hx => he ?_⟩⟩
    · exact injective_principalInclusionRDC K w (hw.trans hιtop.symm)
    · exact injective_principalInclusionRDC K w (he.trans hιx.symm)
    · exact (congrArg _ ht).trans hιtop
    · exact (congrArg _ hx).trans hιx
  have hxU : ∀ α, T.ogp.boundary (LowerSet.Iic x') 0 α = T.ogp.boundary ⊤ 0 α := by
    intro α
    rw [← T.Iic_top]
    refine map_injective ι ?_
    rw [map_boundary, map_boundary, map_Iic, map_Iic, hιx, hιtop]
    exact hK α
  obtain ⟨m, ⟨E⟩⟩ := exists_markedHornData_iso_markedAbove_hornInclusion h x' rfl hxU
  have := MorphismProperty.respectsIso_of_isStableUnderComposition
    (markedExactCylinder.{u}.isomorphisms_le_weakEquivalences (coinductiveGenerators n))
  have hm : markedExactCylinder.{u}.weakEquivalences (coinductiveGenerators n)
      (markedHornInclusion m) :=
    markedExactCylinder.{u}.anodyne_le_weakEquivalences _ (coinductiveGenerators_le_monomorphisms n)
      _ (markedExactCylinder.{u}.le_anodyne _ _
        ((le_sup_left.trans le_sup_left : markedHorns ≤ coinductiveGenerators n) _
          (MorphismProperty.ofHoms.mk m)))
  have E' : Arrow.mk ((MarkedDiagSet.markedAboveFunctor 1).map
      (realize.map (RDCpx.inclusion K hSw))) ≅
      Arrow.mk ((MarkedDiagSet.markedAboveFunctor 1).map (hornInclusion h.toHornData)) :=
    (MarkedDiagSet.markedAboveFunctor 1).mapArrow.mapIso
      (realizeRestrictPrincipalArrowIso K w hSw (hornSubset h.toHornData) hS')
  exact ((markedExactCylinder.{u}.weakEquivalences _).arrow_mk_iso_iff E').2
    (((markedExactCylinder.{u}.weakEquivalences _).arrow_mk_iso_iff E).1 hm)

end Ambient

section Join

variable (n : ℕ∞) (U : MoleculeShape) {Q : OGP.{0}} (hQ : IsMolecule Q)

private def AcyclicJoin (B B' : LowerSet Q) (P P' : LowerSet U.ogp) : Prop :=
  AcyclicIn.{u} n (MoleculeShape.joinRDC U Q hQ)
    (A := MoleculeShape.leibnizJoinSubset U hQ P P' B B') (A' := MoleculeShape.joinPair U hQ P' B')
    inf_le_left

variable {n U hQ} {B B' : LowerSet Q}

private theorem acyclicJoin_of_eq {P P' : LowerSet U.ogp} (e : P = P') :
    AcyclicJoin.{u} n U hQ B B' P P' := by
  subst e
  exact acyclicIn_of_eq (MoleculeShape.leibnizJoinSubset_self_left U hQ P B B')

private theorem acyclicJoin_congr {P P' R R' : LowerSet U.ogp} (e : P = R) (e' : P' = R') :
    AcyclicJoin.{u} n U hQ B B' P P' ↔ AcyclicJoin.{u} n U hQ B B' R R' := by
  subst e e'
  rfl

private theorem AcyclicJoin.trans {P P' P'' : LowerSet U.ogp} (hP : P ≤ P') (hP' : P' ≤ P'')
    (h₁ : AcyclicJoin.{u} n U hQ B B' P P') (h₂ : AcyclicJoin.{u} n U hQ B B' P' P'') :
    AcyclicJoin.{u} n U hQ B B' P P'' := by
  have hc := acyclicIn_sup_right (R := MoleculeShape.leibnizJoinSubset U hQ P P'' B B')
    (A := MoleculeShape.leibnizJoinSubset U hQ P P' B B') (A' := MoleculeShape.joinPair U hQ P' B')
    inf_le_left (MoleculeShape.joinPair_inf_leibnizJoinSubset_left U hQ hP hP' B B').le h₁
  have hc' : AcyclicIn.{u} n (MoleculeShape.joinRDC U Q hQ)
      (MoleculeShape.leibnizJoinSubset_mono U hQ hP le_rfl le_rfl le_rfl :
        MoleculeShape.leibnizJoinSubset U hQ P P'' B B' ≤
          MoleculeShape.leibnizJoinSubset U hQ P' P'' B B') :=
    (acyclicIn_congr
      (sup_eq_right.2 (MoleculeShape.leibnizJoinSubset_mono U hQ le_rfl hP' le_rfl le_rfl))
      (by rw [sup_comm, MoleculeShape.leibnizJoinSubset_sup_joinPair_left U hQ hP hP'])).1 hc
  exact hc'.trans h₂

private theorem acyclicJoin_sup {A A' C C' : LowerSet U.ogp} (h : A ≤ A') (h' : C ≤ C')
    (h₀ : AcyclicJoin.{u} n U hQ B B' (A ⊓ C) (A' ⊓ C'))
    (h₁ : AcyclicJoin.{u} n U hQ B B' A A') (h₂ : AcyclicJoin.{u} n U hQ B B' C C') :
    AcyclicJoin.{u} n U hQ B B' (A ⊔ C) (A' ⊔ C') := by
  have hu := acyclicIn_sup (n := n) (K := MoleculeShape.joinRDC U Q hQ)
    (inf_le_left : MoleculeShape.leibnizJoinSubset U hQ A A' B B' ≤
      MoleculeShape.joinPair U hQ A' B')
    (inf_le_left : MoleculeShape.leibnizJoinSubset U hQ C C' B B' ≤
      MoleculeShape.joinPair U hQ C' B')
    ((acyclicIn_congr (MoleculeShape.leibnizJoinSubset_inf_left U hQ h h' B B').symm
      (by rw [← MoleculeShape.joinPair_inf, inf_idem] : MoleculeShape.joinPair U hQ (A' ⊓ C') B' =
        MoleculeShape.joinPair U hQ A' B' ⊓ MoleculeShape.joinPair U hQ C' B')).1 h₀) h₁ h₂
  exact (acyclicIn_congr (MoleculeShape.leibnizJoinSubset_sup_left U hQ h h' B B')
    (MoleculeShape.joinPair_sup_left U hQ A' C' B').symm).1 hu

private theorem acyclicJoin_sup_right {P P' : LowerSet U.ogp} (R : LowerSet U.ogp) (hP : P ≤ P')
    (hR : P' ⊓ R ≤ P) (h : AcyclicJoin.{u} n U hQ B B' P P') :
    AcyclicJoin.{u} n U hQ B B' (P ⊔ R) (P' ⊔ R) :=
  acyclicJoin_sup hP le_rfl
    (acyclicJoin_of_eq (le_antisymm (inf_le_inf hP le_rfl) (le_inf hR inf_le_right))) h
    (acyclicJoin_of_eq rfl)

private theorem acyclicJoin_of_eq_right (e : B = B') (P P' : LowerSet U.ogp) :
    AcyclicJoin.{u} n U hQ B B' P P' := by
  subst e
  exact acyclicIn_of_eq (MoleculeShape.leibnizJoinSubset_self_right U hQ P P' B)

private theorem AcyclicJoin.trans_right {P P' : LowerSet U.ogp} (hP : P ≤ P')
    {B₁ B₂ B₃ : LowerSet Q} (h₁₂ : B₁ ≤ B₂) (h₂₃ : B₂ ≤ B₃)
    (h₁ : AcyclicJoin.{u} n U hQ B₁ B₂ P P') (h₂ : AcyclicJoin.{u} n U hQ B₂ B₃ P P') :
    AcyclicJoin.{u} n U hQ B₁ B₃ P P' := by
  have hc := acyclicIn_sup_right (R := MoleculeShape.leibnizJoinSubset U hQ P P' B₁ B₃)
    (A := MoleculeShape.leibnizJoinSubset U hQ P P' B₁ B₂) (A' := MoleculeShape.joinPair U hQ P' B₂)
    inf_le_left (MoleculeShape.joinPair_inf_leibnizJoinSubset_right U hQ hP h₁₂ h₂₃).le h₁
  have hc' : AcyclicIn.{u} n (MoleculeShape.joinRDC U Q hQ)
      (MoleculeShape.leibnizJoinSubset_mono U hQ le_rfl le_rfl h₁₂ le_rfl :
        MoleculeShape.leibnizJoinSubset U hQ P P' B₁ B₃ ≤
          MoleculeShape.leibnizJoinSubset U hQ P P' B₂ B₃) :=
    (acyclicIn_congr
      (sup_eq_right.2 (MoleculeShape.leibnizJoinSubset_mono U hQ le_rfl le_rfl le_rfl h₂₃))
      (by rw [sup_comm, MoleculeShape.leibnizJoinSubset_sup_joinPair_right U hQ hP h₁₂ h₂₃])).1 hc
  exact hc'.trans h₂

end Join

section Horn

variable {n : ℕ∞} {U : MoleculeShape} {Q : OGP.{0}} {hQ : IsMolecule Q}

private theorem mem_erase_Iic {α : Type*} [PartialOrder α] {y z : α} :
    z ∈ (LowerSet.Iic y).erase y ↔ z ≤ y ∧ z ≠ y := by
  simp only [← SetLike.mem_coe, LowerSet.coe_erase, LowerSet.coe_Iic, UpperSet.coe_Ici,
    Set.mem_sdiff, Set.mem_Iic, Set.mem_Ici]
  exact ⟨fun h => ⟨h.1, fun hzy => h.2 hzy.ge⟩,
    fun h => ⟨h.1, fun hyz => h.2 (le_antisymm h.1 hyz)⟩⟩

private theorem mem_erase_erase_Iic {t x : U.ogp} (hxt : x ⋖ t) {y : U.ogp} :
    y ∈ ((LowerSet.Iic t).erase t).erase x ↔ y ≤ t ∧ y ≠ t ∧ y ≠ x := by
  simp only [← SetLike.mem_coe, LowerSet.coe_erase, LowerSet.coe_Iic, UpperSet.coe_Ici,
    Set.mem_sdiff, Set.mem_Iic, Set.mem_Ici]
  constructor
  · rintro ⟨⟨hyt, hty⟩, hxy⟩
    exact ⟨hyt, fun h => hty h.ge, fun h => hxy h.ge⟩
  · rintro ⟨hyt, hyt', hyx⟩
    exact ⟨⟨hyt, fun h => hyt' (le_antisymm hyt h)⟩,
      fun h => hyx ((hxt.eq_or_eq h hyt).resolve_right hyt')⟩

private theorem forall_coe_eq_mem_Iic {α : Type*} [PartialOrder α] {t : α} {o : WithBot α} :
    (∀ c : α, o = (c : WithBot α) → c ∈ LowerSet.Iic t) ↔ o ≤ (t : WithBot α) := by
  induction o using WithBot.recBotCoe with
  | bot => exact ⟨fun _ => bot_le, fun _ _ h => absurd h WithBot.bot_ne_coe⟩
  | coe c => simp only [WithBot.coe_inj, forall_eq', LowerSet.mem_Iic_iff, WithBot.coe_le_coe]

private theorem forall_coe_eq_mem_erase_Iic {α : Type*} [PartialOrder α] {y : α} {o : WithBot α}
    (ho : o ≤ (y : WithBot α)) :
    (∀ c : α, o = (c : WithBot α) → c ∈ (LowerSet.Iic y).erase y) ↔ o ≠ (y : WithBot α) := by
  induction o using WithBot.recBotCoe with
  | bot => exact ⟨fun _ => WithBot.bot_ne_coe, fun _ _ h => absurd h WithBot.bot_ne_coe⟩
  | coe c =>
    simp only [WithBot.coe_inj, forall_eq', mem_erase_Iic, Ne]
    exact ⟨And.right, fun h => ⟨WithBot.coe_le_coe.1 ho, h⟩⟩

private theorem forall_coe_eq_mem_erase_erase_Iic {t x : U.ogp} (hxt : x ⋖ t)
    {o : WithBot U.ogp} (ho : o ≤ (t : WithBot _)) :
    (∀ c : U.ogp, o = (c : WithBot _) → c ∈ ((LowerSet.Iic t).erase t).erase x) ↔
      o ≠ (t : WithBot _) ∧ o ≠ (x : WithBot _) := by
  induction o using WithBot.recBotCoe with
  | bot => exact ⟨fun _ => ⟨WithBot.bot_ne_coe, WithBot.bot_ne_coe⟩,
      fun _ _ h => absurd h WithBot.bot_ne_coe⟩
  | coe c =>
    simp only [WithBot.coe_inj, forall_eq', mem_erase_erase_Iic hxt, Ne]
    exact ⟨And.right, fun h => ⟨WithBot.coe_le_coe.1 ho, h⟩⟩

private theorem mem_joinPair_Iic {t : U.ogp} {y : Q}
    (p : (MoleculeShape.joinRDC U Q hQ).obj.toOGP) :
    p ∈ MoleculeShape.joinPair U hQ (LowerSet.Iic t) (LowerSet.Iic y) ↔
      p.1.1 ≤ (t : WithBot _) ∧ p.1.2 ≤ (y : WithBot _) := by
  rw [MoleculeShape.mem_joinPair, forall_coe_eq_mem_Iic, forall_coe_eq_mem_Iic]

private theorem mem_leibnizJoinSubset_horn {t x : U.ogp} (hxt : x ⋖ t) (y : Q)
    (p : (MoleculeShape.joinRDC U Q hQ).obj.toOGP) :
    p ∈ MoleculeShape.leibnizJoinSubset U hQ (((LowerSet.Iic t).erase t).erase x)
        (LowerSet.Iic t) ((LowerSet.Iic y).erase y) (LowerSet.Iic y) ↔
      (p.1.1 ≤ (t : WithBot _) ∧ p.1.2 ≤ (y : WithBot _)) ∧
        ¬(p.1.1 = (t : WithBot _) ∧ p.1.2 = (y : WithBot _)) ∧
        ¬(p.1.1 = (x : WithBot _) ∧ p.1.2 = (y : WithBot _)) := by
  rw [MoleculeShape.mem_leibnizJoinSubset U hQ (fun z hz => LowerSet.mem_Iic_iff.2
    ((mem_erase_erase_Iic hxt).1 hz).1) LowerSet.erase_le, mem_joinPair_Iic]
  refine and_congr_right fun hpw => ?_
  rw [forall_coe_eq_mem_erase_Iic hpw.2, forall_coe_eq_mem_erase_erase_Iic hxt hpw.1]
  tauto

private theorem acyclicJoin_horn_atom {t x : U.ogp} (hxt : x ⋖ t)
    (hs : U.ogp.boundary (LowerSet.Iic x) 0 false = U.ogp.boundary (LowerSet.Iic t) 0 false)
    (y : Q) :
    AcyclicJoin.{u} n U hQ ((LowerSet.Iic y).erase y) (LowerSet.Iic y)
      (((LowerSet.Iic t).erase t).erase x) (LowerSet.Iic t) := by
  let K := MoleculeShape.joinRDC U Q hQ
  classical
  have : Finite Q := Set.finite_univ_iff.1 (LowerSet.coe_top (α := Q) ▸ hQ.finite)
  have : Fintype Q := Fintype.ofFinite Q
  let : FinEnum Q := FinEnum.ofList Finset.univ.toList fun z => Finset.mem_toList.2
    (Finset.mem_univ z)
  let w : K.obj.toOGP :=
    ⟨((t : WithBot _), (y : WithBot _)), fun h => WithBot.coe_ne_bot (congrArg Prod.fst h)⟩
  let e : K.obj.toOGP :=
    ⟨((x : WithBot _), (y : WithBot _)), fun h => WithBot.coe_ne_bot (congrArg Prod.fst h)⟩
  have hew : e ≤ w := join_le_iff.2 ⟨WithBot.coe_le_coe.2 hxt.le, le_rfl⟩
  have hcl : MoleculeShape.joinPair U hQ (LowerSet.Iic t) (LowerSet.Iic y) = LowerSet.Iic w :=
    SetLike.ext fun p => ((mem_joinPair_Iic p).trans
      (join_le_iff (P := U.ogp) (Q := Q) (p := p) (q := w)).symm).trans LowerSet.mem_Iic_iff.symm
  have hbox : ∀ p, p ∈ MoleculeShape.leibnizJoinSubset U hQ (((LowerSet.Iic t).erase t).erase x)
      (LowerSet.Iic t) ((LowerSet.Iic y).erase y) (LowerSet.Iic y) ↔ p ≤ w ∧ p ≠ w ∧ p ≠ e := by
    intro p
    rw [mem_leibnizJoinSubset_horn hxt y p]
    refine and_congr (join_le_iff (P := U.ogp) (Q := Q) (p := p) (q := w)).symm
      (and_congr (not_congr ?_) (not_congr ?_)) <;>
    exact ⟨fun h => Subtype.ext (Prod.ext h.1 h.2),
      fun h => ⟨congrArg (fun q : K.obj.toOGP => q.1.1) h,
        congrArg (fun q : K.obj.toOGP => q.1.2) h⟩⟩
  have hdx : grade ℕ x + 1 = grade ℕ t := Nat.covBy_iff_add_one_eq.1 (hxt.grade ℕ)
  have hdw : grade ℕ w = grade ℕ t + 1 + (grade ℕ y + 1) - 1 := rfl
  have hde : grade ℕ e = grade ℕ x + 1 + (grade ℕ y + 1) - 1 := rfl
  have hK : ∀ α, K.obj.toOGP.boundary (LowerSet.Iic e) 0 α =
      K.obj.toOGP.boundary (LowerSet.Iic w) 0 α := by
    intro α
    cases α
    · have h₁ := boundary_Iic_join_zero_false (P := U.ogp) (Q := Q) e x rfl
      have h₂ := boundary_Iic_join_zero_false (P := U.ogp) (Q := Q) w t rfl
      rw [hs] at h₁
      exact h₁.trans h₂.symm
    · exact (boundary_Iic_join_zero_true (P := U.ogp) (Q := Q) e y rfl).trans
        (boundary_Iic_join_zero_true (P := U.ogp) (Q := Q) w y rfl).symm
  have hSx : MoleculeShape.leibnizJoinSubset U hQ (((LowerSet.Iic t).erase t).erase x)
      (LowerSet.Iic t) ((LowerSet.Iic y).erase y) (LowerSet.Iic y) ≤ LowerSet.Iic w :=
    fun p hp => LowerSet.mem_Iic_iff.2 ((hbox p).1 hp).1
  refine (acyclicIn_congr (h' := hSx) rfl hcl).2 ?_
  exact acyclicIn_horn (GradeOrder.covBy_of_le_of_grade_eq_add_one hew (by omega)) hK hbox hSx

end Horn

section Relative

variable {n : ℕ∞} {U : MoleculeShape} {Q : OGP.{0}} {hQ : IsMolecule Q}

private theorem acyclicJoin_sup_Iic {P P' : LowerSet U.ogp} (hP : P ≤ P') {B : LowerSet Q}
    {y : Q} (hy : B ⊓ LowerSet.Iic y = (LowerSet.Iic y).erase y)
    (h : AcyclicJoin.{u} n U hQ ((LowerSet.Iic y).erase y) (LowerSet.Iic y) P P') :
    AcyclicJoin.{u} n U hQ B (B ⊔ LowerSet.Iic y) P P' := by
  rw [← hy] at h
  have hc := acyclicIn_sup_right (R := MoleculeShape.joinPair U hQ P' B)
    (A := MoleculeShape.leibnizJoinSubset U hQ P P' (B ⊓ LowerSet.Iic y) (LowerSet.Iic y))
    (A' := MoleculeShape.joinPair U hQ P' (LowerSet.Iic y)) inf_le_left
    ((MoleculeShape.joinPair_inf U hQ P' P' _ _).symm.le.trans
      ((MoleculeShape.joinPair_mono U hQ inf_le_left (le_inf inf_le_right inf_le_left)).trans
        (MoleculeShape.joinPair_le_leibnizJoinSubset U hQ P P' inf_le_right))) h
  exact (acyclicIn_congr
    (by rw [MoleculeShape.leibnizJoinSubset_sup_right_eq U hQ hP, sup_comm])
    (by rw [MoleculeShape.joinPair_sup_right, sup_comm])).1 hc

private theorem acyclicJoin_of_forall_atom {P P' : LowerSet U.ogp} (hP : P ≤ P')
    (h : ∀ y : Q, AcyclicJoin.{u} n U hQ ((LowerSet.Iic y).erase y) (LowerSet.Iic y) P P')
    {B B' : LowerSet Q} (hB : B ≤ B') : AcyclicJoin.{u} n U hQ B B' P P' := by
  have hfin : ∀ S : Set Q, S.Finite := fun _ =>
    hQ.finite.subset fun _ _ => LowerSet.mem_top
  obtain ⟨N, hN⟩ : ∃ N, ((B' : Set Q) \ B).ncard = N := ⟨_, rfl⟩
  induction N using Nat.strong_induction_on generalizing B with
  | _ N ih =>
    by_cases hBB : B = B'
    · exact acyclicJoin_of_eq_right hBB P P'
    have hne : ((B' : Set Q) \ B).Nonempty := by
      rw [Set.nonempty_iff_ne_empty, Ne, Set.sdiff_eq_empty]
      exact fun hc => hBB (le_antisymm hB (LowerSet.coe_subset_coe.1 hc))
    obtain ⟨y, ⟨hyB', hyB⟩, hmin⟩ := Set.exists_min_image _ (grade ℕ) (hfin _) hne
    have hy : B ⊓ LowerSet.Iic y = (LowerSet.Iic y).erase y := by
      refine SetLike.ext fun z => ?_
      rw [LowerSet.mem_inf_iff, LowerSet.mem_Iic_iff, mem_erase_Iic]
      refine ⟨fun hz => ⟨hz.2, fun hzy => hyB (hzy ▸ hz.1)⟩, fun hz => ⟨?_, hz.1⟩⟩
      by_contra hzB
      exact not_lt.2 (hmin z ⟨B'.lower hz.1 hyB', hzB⟩)
        (grade_strictMono (lt_of_le_of_ne hz.1 hz.2))
    have hle : B ⊔ LowerSet.Iic y ≤ B' := sup_le hB fun z hz => B'.lower hz hyB'
    have hlt : ((B' : Set Q) \ (B ⊔ LowerSet.Iic y : LowerSet Q)).ncard < N := by
      refine hN ▸ Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset
        (Set.sdiff_subset_sdiff_right (LowerSet.coe_subset_coe.2 le_sup_left))).2
          ⟨y, ⟨hyB', hyB⟩, fun hy' => hy'.2 (LowerSet.mem_sup_iff.2
            (Or.inr (LowerSet.mem_Iic_iff.2 le_rfl)))⟩) (hfin _)
    exact AcyclicJoin.trans_right hP le_sup_left hle (acyclicJoin_sup_Iic hP hy (h y))
      (ih _ hlt hle rfl)

private theorem acyclicJoin_horn {t x : U.ogp} (hxt : x ⋖ t)
    (hs : U.ogp.boundary (LowerSet.Iic x) 0 false = U.ogp.boundary (LowerSet.Iic t) 0 false)
    {B B' : LowerSet Q} (hB : B ≤ B') :
    AcyclicJoin.{u} n U hQ B B' (((LowerSet.Iic t).erase t).erase x) (LowerSet.Iic t) :=
  acyclicJoin_of_forall_atom
    (fun _ hz => LowerSet.mem_Iic_iff.2 ((mem_erase_erase_Iic hxt).1 hz).1)
    (acyclicJoin_horn_atom hxt hs) hB

end Relative

section Induction

variable {n : ℕ∞} {U : MoleculeShape} {Q : OGP.{0}} {hQ : IsMolecule Q} {B B' : LowerSet Q}

private def JoinClaims (n : ℕ∞) (U : MoleculeShape) {Q : OGP.{0}} (hQ : IsMolecule Q)
    (B B' : LowerSet Q) (m : ℕ) : Prop :=
  (∀ W : LowerSet U.ogp, IsMoleculeIn U.ogp W → krullDim W ≤ m →
    ∀ (k : ℕ) (α : Bool), (α = true ∨ 1 ≤ k) →
      AcyclicJoin.{u} n U hQ B B' (U.ogp.boundary W k α) W) ∧
  (∀ W V : LowerSet U.ogp, IsMoleculeIn U.ogp W → krullDim W ≤ m → U.ogp.IsRound W →
    ∀ hV : U.ogp.IsRewritableSubmolecule V W,
      (1 ≤ krullDim W → U.ogp.boundary V 0 false = U.ogp.boundary W 0 false) →
        AcyclicJoin.{u} n U hQ B B' (U.ogp.bdryFull W) hV.complement)

private theorem acyclicJoin_boundary_atom (hB : B ≤ B') {m : ℕ}
    (ih : ∀ m' < m, JoinClaims.{u} n U hQ B B' m')
    {t : U.ogp} (hr : U.ogp.IsRound (LowerSet.Iic t)) (hm : grade ℕ t ≤ m)
    (hpos : 0 < grade ℕ t) (β : Bool) (hβ : β = true ∨ 2 ≤ grade ℕ t) :
    AcyclicJoin.{u} n U hQ B B' (U.ogp.boundary (LowerSet.Iic t) (grade ℕ t - 1) β)
      (LowerSet.Iic t) := by
  have hW : IsMoleculeIn U.ogp (LowerSet.Iic t) := (U.isMolecule.isAtomIn_Iic LowerSet.mem_top).1
  have hd : krullDim (LowerSet.Iic t) = (grade ℕ t - 1 : ℕ) + 1 := by
    rw [LowerSet.krullDim_Iic, ← Nat.cast_add_one, Nat.sub_add_cancel hpos]
  have hbd : ∀ γ, U.ogp.boundary (LowerSet.Iic t) (grade ℕ t - 1) γ =
      U.ogp.bdry (LowerSet.Iic t) γ := fun γ => (bdry_eq_boundary hd γ).symm
  have hlt : ∀ y, y ∈ U.ogp.bdry (LowerSet.Iic t) false ∨ y ∈ U.ogp.bdry (LowerSet.Iic t) true ↔
      y < t := fun y => by
    rw [← LowerSet.mem_sup_iff, ← SetLike.mem_coe, coe_bdry_Iic_sup, Set.mem_Iio]
  rcases Nat.lt_or_ge (grade ℕ t) 2 with h1 | h2
  · obtain rfl : β = true := hβ.resolve_right (by omega)
    obtain ⟨v, hvmin, hv⟩ := exists_boundary_zero_eq_Iic hW false
    have h0 : grade ℕ t - 1 = 0 := by omega
    rw [h0] at hbd
    have hvt' : v ≤ t := LowerSet.mem_Iic_iff.1
      (boundary_le _ 0 false (hv ▸ LowerSet.mem_Iic_iff.2 le_rfl))
    have hv0 : grade ℕ v = 0 := grade_eq_zero_iff.2 hvmin
    have hvt : v ⋖ t := GradeOrder.covBy_of_le_of_grade_eq_add_one hvt' (by omega)
    have hs : U.ogp.boundary (LowerSet.Iic v) 0 false =
        U.ogp.boundary (LowerSet.Iic t) 0 false := by
      rw [hv, boundary_Iic_of_isMin hvmin 0 false]
    have hdisj := boundary_zero_true_inf_false_eq_bot hW
      (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hpos)
    refine (acyclicJoin_congr ?_ rfl).1 (acyclicJoin_horn hvt hs hB)
    refine SetLike.ext fun y => ?_
    rw [mem_erase_erase_Iic hvt, h0]
    constructor
    · rintro ⟨hyt, hyt', hyv⟩
      rcases (hlt y).2 (lt_of_le_of_ne hyt hyt') with hy | hy
      · rw [← hbd, hv, LowerSet.mem_Iic_iff] at hy
        exact absurd (le_antisymm hy (hvmin hy)) hyv
      · rwa [← hbd] at hy
    · intro hy
      have hyt := (hlt y).1 (Or.inr (hbd true ▸ hy))
      refine ⟨hyt.le, hyt.ne, fun hyv => ?_⟩
      have hmem : y ∈ U.ogp.boundary (LowerSet.Iic t) 0 true ⊓
          U.ogp.boundary (LowerSet.Iic t) 0 false :=
        LowerSet.mem_inf_iff.2 ⟨hy, hv ▸ LowerSet.mem_Iic_iff.2 hyv.le⟩
      rw [hdisj] at hmem
      exact hmem
  · obtain ⟨x, hxmax, hxs, hxrw⟩ := exists_maximal_boundary_boundary_Iic_zero_eq hW hr
      (n := grade ℕ t - 1) (by omega) (!β) false
    have hxB := hxmax.prop
    have hBm := hW.boundary (grade ℕ t - 1) (!β)
    have hBr := hr.boundary (grade ℕ t - 1) (!β)
    have hBd : krullDim (U.ogp.boundary (LowerSet.Iic t) (grade ℕ t - 1) (!β)) =
        (grade ℕ t - 1 : ℕ) :=
      hW.krullDim_boundary (by rw [LowerSet.krullDim_Iic]; exact_mod_cast Nat.sub_le _ 1) _
    have hdx : grade ℕ x = grade ℕ t - 1 := hBr.grade_eq_of_maximal hBd hxmax
    have hxW : x ≤ t := LowerSet.mem_Iic_iff.1 (boundary_le _ _ _ hxB)
    have hxt : x ⋖ t := GradeOrder.covBy_of_le_of_grade_eq_add_one hxW (by omega)
    have h₁ := (ih (grade ℕ t - 1) (by omega)).2 _ _ hBm hBd.le hBr hxrw (fun _ => by
      rw [hxs, hr.isGlobular 0 (grade ℕ t - 1) (by omega) false (!β)])
    obtain ⟨-, hhalf, hinf⟩ := hr.halves (n := grade ℕ t - 1) (by omega) fun γ =>
      (hW.bdry (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hpos) γ).nonempty
    have hWR : U.ogp.boundary (LowerSet.Iic t) (grade ℕ t - 1) (!β) ⊓
        U.ogp.boundary (LowerSet.Iic t) (grade ℕ t - 1) β =
        U.ogp.bdryFull (U.ogp.boundary (LowerSet.Iic t) (grade ℕ t - 1) (!β)) := by
      rw [hbd, hbd]
      cases β
      · change U.ogp.bdry _ true ⊓ U.ogp.bdry _ false = U.ogp.bdryFull (U.ogp.bdry _ true)
        rw [inf_comm, hinf, bdryFull, bdryFull, hhalf false, hhalf true]
      · exact hinf
    have hxR : x ∉ U.ogp.boundary (LowerSet.Iic t) (grade ℕ t - 1) β := fun hxR => by
      have hx' : x ∈ U.ogp.bdryFull (U.ogp.boundary (LowerSet.Iic t) (grade ℕ t - 1) (!β)) :=
        hWR ▸ LowerSet.mem_inf_iff.2 ⟨hxB, hxR⟩
      rcases LowerSet.mem_sup_iff.1 hx' with h | h <;>
      · have h' := grade_lt_of_mem_bdry h
        rw [hBd] at h'
        have : grade ℕ x < grade ℕ t - 1 := by exact_mod_cast h'
        omega
    have h₂ := acyclicJoin_sup_right (U.ogp.boundary (LowerSet.Iic t) (grade ℕ t - 1) β)
      hxrw.bdryFull_le_complement
      ((inf_le_inf_right _ fun y hy => hy.1).trans hWR.le) h₁
    have hint : U.ogp.interior (LowerSet.Iic x) = {x} :=
      (U.isMolecule.isAtomIn_Iic LowerSet.mem_top).1.interior_Iic
    have hΛ : ((LowerSet.Iic t).erase t).erase x =
        hxrw.complement ⊔ U.ogp.boundary (LowerSet.Iic t) (grade ℕ t - 1) β := by
      refine SetLike.ext fun y => ?_
      rw [mem_erase_erase_Iic hxt, LowerSet.mem_sup_iff, IsSubmoleculeOf.mem_complement, hint,
        Set.mem_singleton_iff]
      have hy : ∀ γ, y ∈ U.ogp.boundary (LowerSet.Iic t) (grade ℕ t - 1) γ → y < t := fun γ hy =>
        (hlt y).1 (LowerSet.mem_sup_iff.1 (bdry_le_bdryFull _ γ ((hbd γ).le hy)))
      constructor
      · rintro ⟨hyt, hyt', hyx⟩
        rcases (hlt y).2 (lt_of_le_of_ne hyt hyt') with hy' | hy' <;> cases β
        · exact Or.inr (by rwa [hbd])
        · exact Or.inl ⟨by rwa [hbd], hyx⟩
        · exact Or.inl ⟨by rwa [hbd], hyx⟩
        · exact Or.inr (by rwa [hbd])
      · rintro (⟨hy', hyx⟩ | hy')
        · exact ⟨(hy _ hy').le, (hy _ hy').ne, hyx⟩
        · exact ⟨(hy _ hy').le, (hy _ hy').ne, fun hyx => hxR (hyx ▸ hy')⟩
    have hR : U.ogp.bdryFull (U.ogp.boundary (LowerSet.Iic t) (grade ℕ t - 1) (!β)) ⊔
        U.ogp.boundary (LowerSet.Iic t) (grade ℕ t - 1) β =
        U.ogp.boundary (LowerSet.Iic t) (grade ℕ t - 1) β :=
      sup_eq_right.2 (hWR.symm.le.trans inf_le_right)
    have h₃ := (acyclicJoin_congr hR hΛ.symm).1 h₂
    exact AcyclicJoin.trans (le_sup_right.trans hΛ.symm.le)
      (fun y hy => LowerSet.mem_Iic_iff.2 ((mem_erase_erase_Iic hxt).1 hy).1) h₃
      (acyclicJoin_horn hxt hxs hB)

private theorem acyclicJoin_boundary_of_lt (hB : B ≤ B') {m : ℕ}
    (ih : ∀ m' < m, JoinClaims.{u} n U hQ B B' m') :
    ∀ W : LowerSet U.ogp, IsMoleculeIn U.ogp W → krullDim W ≤ m →
      ∀ (k : ℕ) (α : Bool), (α = true ∨ 1 ≤ k) →
        AcyclicJoin.{u} n U hQ B B' (U.ogp.boundary W k α) W := by
  intro W hW
  induction hW with
  | point x hx =>
    intro _ k α _
    refine acyclicJoin_of_eq (boundary_eq_self ?_ α)
    rw [LowerSet.krullDim_Iic_of_isMin hx]
    exact_mod_cast Nat.zero_le k
  | atom t hr _ _ =>
    intro hm k α hα
    have hm' : grade ℕ t ≤ m := by
      rw [LowerSet.krullDim_Iic] at hm
      exact_mod_cast hm
    rcases le_or_gt (grade ℕ t) k with hk | hk
    · exact acyclicJoin_of_eq
        (boundary_eq_self (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hk) α)
    have hpos : 0 < grade ℕ t := by omega
    rcases Nat.lt_or_ge k (grade ℕ t - 1) with hk' | hk'
    · have hstep := acyclicJoin_boundary_atom hB ih hr hm' hpos α (Or.inr (by omega))
      have hWm : IsMoleculeIn U.ogp (LowerSet.Iic t) :=
        (U.isMolecule.isAtomIn_Iic LowerSet.mem_top).1
      have hbb : U.ogp.boundary (U.ogp.boundary (LowerSet.Iic t) (grade ℕ t - 1) α) k α =
          U.ogp.boundary (LowerSet.Iic t) k α :=
        hr.isGlobular k (grade ℕ t - 1) hk' α α
      have hB := (ih (grade ℕ t - 1) (by omega)).1 _ (hWm.boundary _ α)
        (krullDim_boundary_le _ _ _) k α hα
      refine AcyclicJoin.trans ?_ (boundary_le _ _ _) ((acyclicJoin_congr hbb rfl).1 hB) hstep
      rw [← hbb]
      exact boundary_le _ _ _
    · obtain rfl : k = grade ℕ t - 1 := by omega
      exact acyclicJoin_boundary_atom hB ih hr hm' hpos α (hα.imp_right fun h => by omega)
  | paste i V W' W hp hV hW' _ ihV ihW' =>
    intro hm k α hα
    have hmV : krullDim V ≤ m := (LowerSet.krullDim_mono hp.left_le).trans hm
    have hmW' : krullDim W' ≤ m := (LowerSet.krullDim_mono hp.right_le).trans hm
    by_cases hk : krullDim W ≤ k
    · exact acyclicJoin_of_eq (boundary_eq_self hk α)
    rcases le_or_gt k i with hki | hik
    · have key : ∀ A C : LowerSet U.ogp, U.ogp.IsGlobular A → U.ogp.IsGlobular C →
          U.ogp.IsPastingIn i (cond α A C) (cond α C A) W →
          AcyclicJoin.{u} n U hQ B B' (U.ogp.boundary A i α) A →
          AcyclicJoin.{u} n U hQ B B' (U.ogp.boundary C k α) C →
          AcyclicJoin.{u} n U hQ B B' (U.ogp.boundary W k α) W := by
        intro A C hgA hgC hq hjA hjC
        obtain ⟨hs, -, hiA⟩ := (isPastingIn_cond_iff α).1 hq
        have h₃ := (acyclicJoin_congr (sup_eq_right.2 (hiA.symm.le.trans inf_le_right)) hs).1
          (acyclicJoin_sup_right C (boundary_le A i α) hiA.le hjA)
        exact (acyclicJoin_congr (hq.boundary_eq_of_le_cond α hgA hgC hki).symm rfl).1
          (hjC.trans (boundary_le C k α) (hq.le_cond α) h₃)
      have hαi : α = true ∨ 1 ≤ i := hα.imp_right (·.trans hki)
      cases α
      · exact key W' V hW'.isGlobular hV.isGlobular hp (ihW' hmW' i false hαi) (ihV hmV k false hα)
      · exact key V W' hV.isGlobular hW'.isGlobular hp (ihV hmV i true hαi) (ihW' hmW' k true hα)
    · have hbu : U.ogp.boundary W k α = U.ogp.boundary V k α ⊔ U.ogp.boundary W' k α :=
        (hp.boundary_of_lt hV.isGlobular hW'.isGlobular hik α).sup_eq.symm
      have hsV : U.ogp.boundary V i true ≤ U.ogp.boundary V k α := by
        rw [← hV.isGlobular i k hik true α]
        exact boundary_le _ _ _
      have hsW : U.ogp.boundary W' i false ≤ U.ogp.boundary W' k α := by
        rw [← hW'.isGlobular i k hik false α]
        exact boundary_le _ _ _
      have h₀ : AcyclicJoin.{u} n U hQ B B' (U.ogp.boundary V k α ⊓ U.ogp.boundary W' k α)
          (V ⊓ W') :=
        acyclicJoin_of_eq (le_antisymm (inf_le_inf (boundary_le V k α) (boundary_le W' k α))
          (le_inf (hp.inf_eq_output.le.trans hsV) (hp.inf_eq_input.le.trans hsW)))
      exact (acyclicJoin_congr hbu.symm hp.sup_eq).1
        (acyclicJoin_sup (boundary_le V k α) (boundary_le W' k α) h₀ (ihV hmV k α hα)
          (ihW' hmW' k α hα))

private theorem bdry_false_eq_left_of_krullDim_eq_one {W V : LowerSet U.ogp}
    (hV : U.ogp.IsRewritableSubmolecule V W) (b : RewritableBlock U.ogp 0 W V)
    (hd : krullDim W = (0 : ℕ) + 1)
    (hs : U.ogp.boundary V 0 false = U.ogp.boundary W 0 false) :
    U.ogp.bdry W false = b.left := by
  have hL0 : U.ogp.boundary b.left 0 false = U.ogp.boundary W 0 false :=
    (b.paste_right.boundary_input.trans b.paste_left.boundary_input).symm
  have hVm := hV.isSubmoleculeOf.isMoleculeIn
  have hQ0 : U.ogp.boundary b.middle 0 false = U.ogp.boundary V 0 false := by
    obtain ⟨q, hqmin, hq⟩ := exists_boundary_zero_eq_Iic b.isMoleculeIn_middle false
    obtain ⟨v, -, hv⟩ := exists_boundary_zero_eq_Iic hVm false
    have hmeet := b.meet false
    rw [bdry_eq_boundary (hV.krullDim_eq.trans hd) false, hq, hv] at hmeet
    have hvq : v ∈ LowerSet.Iic q ⊓ V := hmeet ▸ LowerSet.mem_Iic_iff.2 le_rfl
    have hvq' : v ≤ q := LowerSet.mem_Iic_iff.1 (LowerSet.mem_inf_iff.1 hvq).1
    rw [hq, hv, le_antisymm hvq' (hqmin hvq')]
  have hL : krullDim b.left = 0 := krullDim_eq_zero_of_boundary_zero_eq b.isMoleculeIn_left
    (by rw [hL0, ← hs, ← hQ0, ← b.paste_left.inf_eq_input, b.paste_left.inf_eq_output])
  rw [bdry_eq_boundary hd false, ← hL0, boundary_eq_self (by rw [hL]; exact_mod_cast le_rfl)]

private theorem acyclicJoin_sdiff_of_lt {m : ℕ} (ih : ∀ m' < m, JoinClaims.{u} n U hQ B B' m')
    (h1 : ∀ W : LowerSet U.ogp, IsMoleculeIn U.ogp W → krullDim W ≤ m →
      ∀ (k : ℕ) (α : Bool), (α = true ∨ 1 ≤ k) →
        AcyclicJoin.{u} n U hQ B B' (U.ogp.boundary W k α) W)
    (W V : LowerSet U.ogp) (hW : IsMoleculeIn U.ogp W) (hm : krullDim W ≤ m)
    (hr : U.ogp.IsRound W) (hV : U.ogp.IsRewritableSubmolecule V W)
    (hs : 1 ≤ krullDim W → U.ogp.boundary V 0 false = U.ogp.boundary W 0 false) :
    AcyclicJoin.{u} n U hQ B B' (U.ogp.bdryFull W) hV.complement := by
  obtain ⟨d, hd⟩ := hW.exists_krullDim_eq
  rcases d with _ | d
  · have hdim0 : krullDim W = 0 := by exact_mod_cast hd
    exact acyclicJoin_of_eq ((bdryFull_eq_bot hdim0.le).trans
      (hV.complement_eq_bot_of_krullDim_eq_zero hdim0).symm)
  have hn' : krullDim W = d + 1 := by rw [hd]; push_cast; rfl
  have hdm : d + 1 ≤ m := by
    rw [hn'] at hm
    exact_mod_cast hm
  have hs' := hs (by rw [hn']; exact_mod_cast Nat.le_add_left 1 d)
  obtain ⟨b⟩ := nonempty_rewritableBlock hV hn'
  obtain ⟨hL, hR, hF, hA⟩ := b.outer_boundary hr hV hn'
  have hI : b.left ⊓ b.right = (b.rewritable false).complement :=
    SetLike.coe_injective (b.coe_inf_eq_complement hV hn')
  have hmL : krullDim b.left ≤ m := (LowerSet.krullDim_mono b.left_le).trans hm
  have hmR : krullDim b.right ≤ m := (LowerSet.krullDim_mono b.right_le).trans hm
  have hRb : U.ogp.bdry W true = U.ogp.boundary b.right d true := by
    rw [bdry_eq_boundary hn', b.paste_right.boundary_output]
  have h₂ : AcyclicJoin.{u} n U hQ B B' (U.ogp.bdry W true) b.right :=
    (acyclicJoin_congr hRb.symm rfl).1 (h1 _ b.isMoleculeIn_right hmR d true (Or.inl rfl))
  have h₁ : AcyclicJoin.{u} n U hQ B B' (U.ogp.bdry W false) b.left := by
    rcases Nat.eq_zero_or_pos d with rfl | hd1
    · exact acyclicJoin_of_eq (bdry_false_eq_left_of_krullDim_eq_one hV b hn' hs')
    · have hLb : U.ogp.bdry W false = U.ogp.boundary b.left d false := by
        rw [bdry_eq_boundary hn', b.paste_right.boundary_input, b.paste_left.boundary_input]
      exact (acyclicJoin_congr hLb.symm rfl).1
        (h1 _ b.isMoleculeIn_left hmL d false (Or.inr hd1))
  have h₀ := (ih d (by omega)).2 _ _ (b.isMoleculeIn_middle.boundary d false) hA.le
    (b.isRound_input hr hn') (b.rewritable false) (fun hd' => by
      have hd0 : 1 ≤ d := by
        rw [hA] at hd'
        exact_mod_cast hd'
      rw [bdry_eq_boundary (hV.krullDim_eq.trans hn') false,
        hV.isRound.isGlobular 0 d hd0 false false, hs', b.boundary_boundary_middle hd0 false])
  have h₀' := (acyclicJoin_congr hF.symm hI.symm).1 h₀
  exact (acyclicJoin_congr rfl
    (SetLike.coe_injective (b.coe_sup_eq_complement hV.isSubmoleculeOf.isMoleculeIn))).1
    (acyclicJoin_sup hL hR h₀' h₁ h₂)

private theorem joinClaims (hB : B ≤ B') : ∀ m, JoinClaims.{u} n U hQ B B' m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have h1 := acyclicJoin_boundary_of_lt hB ih
    exact ⟨h1, acyclicJoin_sdiff_of_lt ih h1⟩

end Induction

theorem weakEquivalence_markedAboveFunctor_map_leibnizJoinBox_boundary (n : ℕ∞)
    (U : MoleculeShape) {Q : OGP.{0}} (hQ : IsMolecule Q) {B B' : LowerSet Q} (hB : B ≤ B')
    (k : ℕ) (α : Bool) (hα : α = true ∨ 1 ≤ k) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map ((MarkedDiagSet.markedAboveFunctor 1).map
      (leibnizJoinBox.{u} U hQ (U.ogp.boundary ⊤ k α) ⊤ B B'))) :=
  (weakEquivalence_coinductive_iff n _).2
    ((joinClaims (n := n) hB U.dimension).1 ⊤ U.isMolecule
      (LowerSet.krullDim_top.trans U.krullDim_eq_dimension).le k α hα)

theorem weakEquivalence_markedAboveFunctor_map_leibnizJoinBox_sdiff_interior (n : ℕ∞)
    (U : MoleculeShape) (hU : U.ogp.IsRound ⊤) {V : LowerSet U.ogp}
    (hV : U.ogp.IsRewritableSubmolecule V ⊤)
    (hs : U.ogp.boundary V 0 false = U.ogp.boundary ⊤ 0 false)
    {Q : OGP.{0}} (hQ : IsMolecule Q) {B B' : LowerSet Q} (hB : B ≤ B') :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map ((MarkedDiagSet.markedAboveFunctor 1).map
      (leibnizJoinBox.{u} U hQ (U.ogp.bdryFull ⊤) hV.complement B B'))) :=
  (weakEquivalence_coinductive_iff n _).2
    ((joinClaims (n := n) hB U.dimension).2 ⊤ V U.isMolecule
      (LowerSet.krullDim_top.trans U.krullDim_eq_dimension).le hU hV fun _ => hs)

theorem weakEquivalence_markedAboveFunctor_map_leibnizJoinBox_horn (n : ℕ∞)
    (U : MoleculeShape) {t x : U.ogp} (hxt : x ⋖ t)
    (hs : U.ogp.boundary (LowerSet.Iic x) 0 false = U.ogp.boundary (LowerSet.Iic t) 0 false)
    {Q : OGP.{0}} (hQ : IsMolecule Q) {B B' : LowerSet Q} (hB : B ≤ B') :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map ((MarkedDiagSet.markedAboveFunctor 1).map
      (leibnizJoinBox.{u} U hQ (((LowerSet.Iic t).erase t).erase x) (LowerSet.Iic t) B B'))) :=
  (weakEquivalence_coinductive_iff n _).2 (acyclicJoin_horn (n := n) (hQ := hQ) hxt hs hB)

private def simplexBoundary (r : ℕ) : LowerSet (simplex.{0} r) where
  carrier := {b | grade ℕ b < r}
  lower' _ _ h hb := by
    simp only [Set.mem_ofPred_eq] at hb ⊢
    exact (grade_mono h).trans_lt hb

private theorem joinSubset_eq_joinPair (U : MoleculeShape) (r : ℕ) (P : LowerSet U.ogp) :
    MoleculeShape.joinSubset U r P = MoleculeShape.joinPair U (isAtom_simplex r).1 P ⊤ :=
  SetLike.ext fun p =>
    ⟨fun h => (MoleculeShape.mem_joinPair U (isAtom_simplex r).1 (p := p)).2
        ⟨(MoleculeShape.mem_joinSubset U r).1 h, fun _ _ => LowerSet.mem_top⟩,
      fun h => (MoleculeShape.mem_joinSubset U r).2
        ((MoleculeShape.mem_joinPair U (isAtom_simplex r).1 (p := p)).1 h).1⟩

private theorem joinBoxSubset_eq_leibnizJoinSubset (U : MoleculeShape) (r : ℕ)
    {P P' : LowerSet U.ogp} (hP : P ≤ P') :
    MoleculeShape.joinBoxSubset U r P P' =
      MoleculeShape.leibnizJoinSubset U (isAtom_simplex r).1 P P' (simplexBoundary r) ⊤ :=
  SetLike.ext fun p =>
    ⟨fun h => (MoleculeShape.mem_leibnizJoinSubset U _ hP le_top (p := p)).2
        ⟨(MoleculeShape.mem_joinPair U (isAtom_simplex r).1 (p := p)).2
          ⟨((MoleculeShape.mem_joinBoxSubset U r).1 h).1, fun _ _ => LowerSet.mem_top⟩,
          ((MoleculeShape.mem_joinBoxSubset U r).1 h).2⟩,
      fun h => (MoleculeShape.mem_joinBoxSubset U r).2
        ⟨((MoleculeShape.mem_joinPair U (isAtom_simplex r).1 (p := p)).1
          ((MoleculeShape.mem_leibnizJoinSubset U _ hP le_top (p := p)).1 h).1).1,
          ((MoleculeShape.mem_leibnizJoinSubset U _ hP le_top (p := p)).1 h).2⟩⟩

theorem weakEquivalence_markedAboveFunctor_map_joinBox_boundary (n : ℕ∞) (U : MoleculeShape)
    (r k : ℕ) (α : Bool) (hα : α = true ∨ 1 ≤ k) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map ((MarkedDiagSet.markedAboveFunctor 1).map
      (joinBox.{u} U r (U.ogp.boundary ⊤ k α) ⊤))) :=
  (weakEquivalence_coinductive_iff n _).2
    ((acyclicIn_congr (K := MoleculeShape.joinSimplexRDC U r)
      (joinBoxSubset_eq_leibnizJoinSubset U r le_top).symm
      (joinSubset_eq_joinPair U r ⊤).symm).1
    ((joinClaims (n := n) (le_top : simplexBoundary r ≤ ⊤) U.dimension).1 ⊤ U.isMolecule
      (LowerSet.krullDim_top.trans U.krullDim_eq_dimension).le k α hα))

theorem weakEquivalence_markedAboveFunctor_map_joinBox_sdiff_interior (n : ℕ∞)
    (U : MoleculeShape) (r : ℕ) (hU : U.ogp.IsRound ⊤) {V : LowerSet U.ogp}
    (hV : U.ogp.IsRewritableSubmolecule V ⊤)
    (hs : U.ogp.boundary V 0 false = U.ogp.boundary ⊤ 0 false) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map ((MarkedDiagSet.markedAboveFunctor 1).map
      (joinBox.{u} U r (U.ogp.bdryFull ⊤) hV.complement))) :=
  (weakEquivalence_coinductive_iff n _).2
    ((acyclicIn_congr (K := MoleculeShape.joinSimplexRDC U r)
      (joinBoxSubset_eq_leibnizJoinSubset U r hV.bdryFull_le_complement).symm
      (joinSubset_eq_joinPair U r _).symm).1
    ((joinClaims (n := n) (le_top : simplexBoundary r ≤ ⊤) U.dimension).2 ⊤ V U.isMolecule
      (LowerSet.krullDim_top.trans U.krullDim_eq_dimension).le hU hV fun _ => hs))

end Atoms.Diagrammatic

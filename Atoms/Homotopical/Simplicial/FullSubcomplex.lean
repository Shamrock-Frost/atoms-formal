import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.FullSubcomplex
import Atoms.Homotopical.Simplicial.FullyFaithful

universe u

open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra

open SSet.modelCategoryJoyal

namespace SSet.modelCategoryJoyal

private lemma rlp_I_fullSubcomplexMap {X Y : SSet.{u}} (f : X ⟶ Y)
    [Fibration f] [WeakEquivalence f] (P : X _⦋0⦌ → Prop) (Q : Y _⦋0⦌ → Prop)
    (hf : ∀ x, P x ↔ Q (f.app _ x)) :
    modelCategoryQuillen.I.rlp (fullSubcomplexMap f P Q (fun x ↦ (hf x).1)) := by
  have hl : modelCategoryQuillen.I.rlp f := by
    rw [← rlp_monomorphisms]
    change (cofibrations SSet.{u}).rlp f
    rw [cofibrations_rlp, mem_trivialFibrations_iff]
    exact ⟨inferInstance, inferInstance⟩
  rintro A B j hj
  have := hl j hj
  refine ⟨fun {a b} sq ↦ ?_⟩
  let sq' : CommSq (a ≫ (X.fullSubcomplex P).ι) j f
      (b ≫ (Y.fullSubcomplex Q).ι) := ⟨by
    rw [Category.assoc, ← fullSubcomplexMap_ι f P Q (fun x ↦ (hf x).1),
      ← Category.assoc, sq.w, Category.assoc]⟩
  have hm : Subcomplex.range sq'.lift ≤ X.fullSubcomplex P := by
    rintro n x ⟨z, rfl⟩ i
    apply (hf _).2
    rw [← sq'.lift.naturality_apply]
    have hw := congrArg (fun t ↦ t.app (op ⦋0⦌)
      (B.map (SimplexCategory.const ⦋0⦌ n.unop i).op z)) sq'.fac_right
    change f.app _ (sq'.lift.app _ _) = _ at hw
    rw [hw]
    exact (mem_fullSubcomplex_obj_zero_iff Q _).1 (b.app _ _).property
  let l := Subcomplex.lift sq'.lift hm
  exact ⟨⟨⟨l, by
    apply (cancel_mono (X.fullSubcomplex P).ι).1
    simpa only [l, Category.assoc, Subcomplex.lift_ι] using sq'.fac_left,
    by
      apply (cancel_mono (Y.fullSubcomplex Q).ι).1
      rw [Category.assoc, fullSubcomplexMap_ι, ← Category.assoc, Subcomplex.lift_ι]
      exact sq'.fac_right⟩⟩⟩

private lemma predicate_iff_of_invStruct {Y : SSet.{u}} (Q : Y _⦋0⦌ → Prop)
    (hQ : ∀ {y y' : Y _⦋0⦌} (e : Edge y y'), Nonempty e.InvStruct → Q y → Q y')
    {y y' : Y _⦋0⦌} (e : Edge y y') (h : Nonempty e.InvStruct) : Q y ↔ Q y' :=
  ⟨hQ e h, hQ h.some.inv ⟨h.some.invStructInv⟩⟩

theorem weakEquivalence_fullSubcomplex_map {X Y : SSet.{u}}
    [X.Quasicategory] [Y.Quasicategory] (f : X ⟶ Y) [WeakEquivalence f]
    (P : X _⦋0⦌ → Prop) (Q : Y _⦋0⦌ → Prop)
    (hPQ : ∀ x, P x ↔ Q (f.app _ x))
    (hQ : ∀ {y y' : Y _⦋0⦌} (e : Edge y y'), Nonempty e.InvStruct → Q y → Q y')
    (g : (X.fullSubcomplex P : SSet.{u}) ⟶ (Y.fullSubcomplex Q : SSet.{u}))
    (hg : g ≫ (Y.fullSubcomplex Q).ι = (X.fullSubcomplex P).ι ≫ f) :
    WeakEquivalence g := by
  classical
  have : IsFibrant X := (isFibrant_iff_quasicategory _).2 inferInstance
  have : IsFibrant Y := (isFibrant_iff_quasicategory _).2 inferInstance
  let h : FibrantBrownFactorization f := Classical.choice inferInstance
  have : IsFibrant h.Z := isFibrant_of_fibration h.p
  have : h.Z.Quasicategory := (isFibrant_iff_quasicategory _).1 inferInstance
  let R : h.Z _⦋0⦌ → Prop := fun z ↦ Q (h.p.app _ z)
  have hR (z : h.Z _⦋0⦌) : R z ↔ P (h.r.app _ z) := by
    obtain ⟨x', ⟨i⟩⟩ := (essSurj_of_weakEquivalence h.i).mem_essImage
      (Truncated.HomotopyCategory.mk z)
    obtain ⟨x, rfl⟩ := Truncated.HomotopyCategory.mk_surjective x'
    obtain ⟨e, he⟩ := Truncated.HomotopyCategory.homMk_surjective
      (A := (truncation 2).obj h.Z) (x := h.i.app _ x) (y := z) i.hom
    have hi : IsIso (Truncated.HomotopyCategory.homMk e) := he ▸ Iso.isIso_hom i
    obtain ⟨I⟩ := (isIso_homMk_iff e).1 hi
    have hp := predicate_iff_of_invStruct Q hQ (Edge.map e h.p) ⟨I.map h.p⟩
    have hr := predicate_iff_of_invStruct Q hQ (Edge.map e (h.r ≫ f)) ⟨I.map (h.r ≫ f)⟩
    have hp0 : h.p.app (op ⦋0⦌) (h.i.app (op ⦋0⦌) x) = f.app (op ⦋0⦌) x :=
      congrArg (fun t ↦ t.app (op ⦋0⦌) x) h.fac
    change Q (h.p.app (op ⦋0⦌) (h.i.app (op ⦋0⦌) x)) ↔ Q (h.p.app _ z) at hp
    change Q ((h.r ≫ f).app (op ⦋0⦌) (h.i.app (op ⦋0⦌) x)) ↔
      Q ((h.r ≫ f).app _ z) at hr
    have hr0 : (h.r ≫ f).app (op ⦋0⦌) (h.i.app (op ⦋0⦌) x) = f.app (op ⦋0⦌) x := by
      change ((h.i ≫ h.r) ≫ f).app (op ⦋0⦌) x = _
      rw [h.i_r, Category.id_comp]
    rw [hp0] at hp
    rw [hr0] at hr
    exact hp.symm.trans (hr.trans (hPQ (h.r.app _ z)).symm)
  have hi (x : X _⦋0⦌) : P x → R (h.i.app _ x) := by
    dsimp only [R]
    rw [← NatTrans.comp_app_apply, h.fac]
    exact (hPQ x).1
  let i' := fullSubcomplexMap h.i P R hi
  let p' := fullSubcomplexMap h.p R Q (fun _ ↦ id)
  let r' := fullSubcomplexMap h.r R P (fun z ↦ (hR z).1)
  have : WeakEquivalence p' := weakEquivalence_of_rlp_I
    (rlp_I_fullSubcomplexMap h.p R Q (fun _ ↦ Iff.rfl))
  have : WeakEquivalence r' := weakEquivalence_of_rlp_I (rlp_I_fullSubcomplexMap h.r R P hR)
  have hir : i' ≫ r' = 𝟙 _ := by
    apply (cancel_mono (X.fullSubcomplex P).ι).1
    dsimp only [i', r']
    rw [Category.assoc, fullSubcomplexMap_ι, ← Category.assoc, fullSubcomplexMap_ι,
      Category.assoc, h.i_r, Category.comp_id, Category.id_comp]
  have : WeakEquivalence i' := weakEquivalence_of_postcomp_of_fac hir
  have hg' : g = i' ≫ p' := by
    apply (cancel_mono (Y.fullSubcomplex Q).ι).1
    rw [hg]
    dsimp only [i', p']
    rw [Category.assoc, fullSubcomplexMap_ι, ← Category.assoc, fullSubcomplexMap_ι,
      Category.assoc, h.fac]
  rw [hg']
  infer_instance

end SSet.modelCategoryJoyal

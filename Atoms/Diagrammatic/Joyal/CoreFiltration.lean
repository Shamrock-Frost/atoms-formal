import Atoms.Diagrammatic.Joyal.HornAttachment
import Atoms.Diagrammatic.SimplicialAdjunction

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Opposite MonoidalCategory Simplicial
open Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape Atoms.Homotopical AugmentedSimplexCategory

universe w u

namespace Atoms.Diagrammatic

variable (X : DiagSet.{u})

private theorem exists_isSplitEpi_isNondegenerate_lanUnit {U : Atom}
    (y : (SSet.toDiagSet.obj (DiagSet.toSSet.obj X)).obj (op U)) :
    ∃ (k : SimplexCategory) (p : U ⟶ simplexFunctor.obj k)
      (w : X.obj (op (simplexFunctor.obj k))), IsSplitEpi p ∧ EZCategory.IsNondegenerate X w ∧
        (SSet.toDiagSet.obj (DiagSet.toSSet.obj X)).map p.op
          ((simplexFunctor.op.lanUnit.app (DiagSet.toSSet.obj X)).app (op k) w) = y := by
  obtain ⟨n, g, z, rfl⟩ := exists_toDiagSet_obj_map_lanUnit_eq _ y
  obtain ⟨V₁, p₁, i₁, hp₁, hi₁, rfl⟩ := EZCategory.exists_factorization g
  obtain ⟨k₁, ⟨φ⟩⟩ := exists_nonempty_iso_simplexFunctor_obj_of_isInclusionHom i₁
    (isInclusionHom_of_mono i₁)
  obtain ⟨θ₁, hθ₁⟩ := simplexFunctor.map_surjective (φ.inv ≫ i₁)
  obtain ⟨V₂, s, w, hs, hw, hsw⟩ := EZCategory.exists_isNondegenerate X _
    (X.map (simplexFunctor.map θ₁).op z)
  obtain ⟨k₂, ⟨ψ⟩⟩ := exists_nonempty_iso_simplexFunctor_obj_of_isCollapseHom s
    (isCollapseHom_of_isSplitEpi s)
  obtain ⟨σ, hσ⟩ := simplexFunctor.map_surjective (s ≫ ψ.hom)
  have : IsSplitEpi (simplexFunctor.map σ) := by
    rw [hσ]
    infer_instance
  refine ⟨k₂, (p₁ ≫ φ.hom) ≫ simplexFunctor.map σ, X.map ψ.inv.op w,
    inferInstance, isNondegenerate_map_hom ψ.symm hw, ?_⟩
  have e₁ : p₁ ≫ i₁ = (p₁ ≫ φ.hom) ≫ simplexFunctor.map θ₁ := by
    rw [hθ₁, Category.assoc, φ.hom_inv_id_assoc]
  have e₂ : X.map (simplexFunctor.map σ).op (X.map ψ.inv.op w) =
      X.map (simplexFunctor.map θ₁).op z := by
    rw [← hsw, ← Functor.map_comp_apply, ← op_comp, hσ, Category.assoc, ψ.hom_inv_id,
      Category.comp_id]
  refine (toDiagSet_obj_map_comp_lanUnit _ _ σ _).trans (Eq.trans ?_
    ((congrArg (fun f => (SSet.toDiagSet.obj (DiagSet.toSSet.obj X)).map f.op
      ((simplexFunctor.op.lanUnit.app (DiagSet.toSSet.obj X)).app (op n) z)) e₁).trans
      (toDiagSet_obj_map_comp_lanUnit _ _ θ₁ _)).symm)
  exact congrArg _ (congrArg _ e₂)

theorem mono_sSetDiagSetAdj_counit_app : Mono (sSetDiagSetAdj.counit.app X) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨U⟩
  rw [mono_iff_injective]
  intro y₁ y₂ h
  obtain ⟨k₁, p₁, w₁, hp₁, hw₁, rfl⟩ := exists_isSplitEpi_isNondegenerate_lanUnit X y₁
  obtain ⟨k₂, p₂, w₂, hp₂, hw₂, rfl⟩ := exists_isSplitEpi_isNondegenerate_lanUnit X y₂
  rw [sSetDiagSetAdj_counit_app_app_map_lanUnit,
    sSetDiagSetAdj_counit_app_app_map_lanUnit] at h
  obtain ⟨e, ⟨he, hew⟩, -⟩ :=
    EZCategory.existsUnique_iso_of_isNondegenerate X p₁ p₂ w₁ w₂ hp₁ hw₁ hp₂ hw₂ h
  obtain ⟨τ, hτ⟩ := simplexFunctor.map_surjective e.hom
  subst he
  rw [← hτ] at hew ⊢
  exact (congrArg _ (congrArg _ hew.symm)).trans
    (toDiagSet_obj_map_comp_lanUnit (DiagSet.toSSet.obj X) p₁ τ w₂).symm

theorem range_sSetDiagSetAdj_counit_app :
    Subfunctor.range (sSetDiagSetAdj.counit.app X) = coreFiltration 1 X := by
  ext ⟨U⟩ x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨n, g, z, rfl⟩ := exists_toDiagSet_obj_map_lanUnit_eq _ y
    let ψ : cone atomPoint n.len ≅ simplexFunctor.obj n := coneAtomPointIso n.len
    refine ⟨atomPoint, n.len, g ≫ ψ.inv, X.map ψ.hom.op z,
      by rw [dimension_atomPoint]; exact zero_le_one,
      Eq.trans ?_ (sSetDiagSetAdj_counit_app_app_map_lanUnit X g z).symm⟩
    have key (z' : X.obj (op (simplexFunctor.obj n))) :
        X.map (g ≫ ψ.inv).op (X.map ψ.hom.op z') = X.map g.op z' := by
      rw [← Functor.map_comp_apply, ← op_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact key z
  · rintro ⟨B, r, f, z, hB, rfl⟩
    obtain ⟨k, ⟨φ⟩⟩ := exists_nonempty_iso_cone_simplexFunctor_obj hB r
    refine ⟨(SSet.toDiagSet.obj (DiagSet.toSSet.obj X)).map (f ≫ φ.hom).op
        ((simplexFunctor.op.lanUnit.app (DiagSet.toSSet.obj X)).app (op k)
          (X.map φ.inv.op z)),
      (sSetDiagSetAdj_counit_app_app_map_lanUnit X _ _).trans ?_⟩
    rw [← Functor.map_comp_apply, ← op_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem exists_iso_comp_coreFiltration_ι_eq_counit_app :
    ∃ e : SSet.toDiagSet.obj (DiagSet.toSSet.obj X) ≅ (coreFiltration 1 X).toFunctor,
      e.hom ≫ (coreFiltration 1 X).ι = sSetDiagSetAdj.counit.app X := by
  have := mono_sSetDiagSetAdj_counit_app X
  rw [← range_sSetDiagSetAdj_counit_app]
  exact ⟨asIso (Subfunctor.toRange _), Subfunctor.toRange_ι _⟩

section Stages

variable (X : DiagSet.{u}) (m : ℕ)
  (con : ∀ B : Atom, IsCore B → B.dimension = m → CoherentContraction B X)

structure FreeCell where
  core : Atom
  isCore : IsCore core
  isoRep_eq : isoRep core = core
  dimension_eq : core.dimension = m
  deg : AugmentedSimplexCategory
  cell : X.obj (op (cone core (card deg)))
  isFree : (con core isCore dimension_eq).IsFree deg cell

namespace FreeCell

variable {X m con} (P : FreeCell X m con)

abbrev contraction : CoherentContraction P.core X := con P.core P.isCore P.dimension_eq

abbrev atom : Atom := cone P.core (card (WithInitial.of ⦋0⦌ ⊗ P.deg))

def top : X.obj (op P.atom) := P.contraction.ext P.deg P.cell

def faceTop : P.atom.ogp :=
  coneHom P.core (toOrderHom (inr (WithInitial.of ⦋0⦌) P.deg)) (cone P.core (card P.deg)).top

theorem map_coneHom_inr_top :
    X.map (coneHom P.core (toOrderHom (inr (WithInitial.of ⦋0⦌) P.deg))).op P.top = P.cell :=
  P.contraction.map_coneHom_inr_ext P.deg P.cell

end FreeCell

def attachStage (n : ℕ) : Subfunctor X where
  obj U := {z | z ∈ (coreFiltration (m - 1) X).obj U ∨
    ∃ (P : FreeCell X m con) (f : U.unop ⟶ P.atom), card P.deg < n ∧ X.map f.op P.top = z}
  map g z hz := by
    rcases hz with hz | ⟨P, f, hP, rfl⟩
    · exact Or.inl ((coreFiltration (m - 1) X).map g hz)
    · refine Or.inr ⟨P, g.unop ≫ f, hP, ?_⟩
      rw [op_comp, Functor.map_comp_apply]
      rfl

variable {X m con}

theorem attachStage_mono {n n' : ℕ} (h : n ≤ n') :
    attachStage X m con n ≤ attachStage X m con n' := by
  rintro U z (hz | ⟨P, f, hP, rfl⟩)
  · exact Or.inl hz
  · exact Or.inr ⟨P, f, by omega, rfl⟩

theorem mem_attachStage_zero {U : Atom} {z : X.obj (op U)} :
    z ∈ (attachStage X m con 0).obj (op U) ↔ z ∈ (coreFiltration (m - 1) X).obj (op U) := by
  refine ⟨fun hz => ?_, Or.inl⟩
  rcases hz with hz | ⟨P, f, hP, -⟩
  · exact hz
  · omega

theorem attachStage_le_coreFiltration (n : ℕ) : attachStage X m con n ≤ coreFiltration m X := by
  rintro U z (hz | ⟨P, f, -, rfl⟩)
  · exact coreFiltration_mono X (Nat.sub_le m 1) _ hz
  · exact ⟨P.core, _, f, P.top, P.dimension_eq.le, rfl⟩

theorem map_top_mem_attachStage (P : FreeCell X m con) {U : Atom} (f : U ⟶ P.atom) {n : ℕ}
    (h : card P.deg < n) : X.map f.op P.top ∈ (attachStage X m con n).obj (op U) :=
  Or.inr ⟨P, f, h, rfl⟩

theorem top_mem_attachStage (P : FreeCell X m con) {n : ℕ} (h : card P.deg < n) :
    P.top ∈ (attachStage X m con n).obj (op P.atom) := by
  have := map_top_mem_attachStage P (𝟙 _) h
  rwa [op_id, Functor.map_id_apply] at this

theorem ext_mem_attachStage {B : Atom} (hB : IsCore B) (hrep : isoRep B = B)
    (hd : B.dimension = m) (h2 : 2 ≤ m) (c : AugmentedSimplexCategory)
    (v : X.obj (op (cone B (card c)))) :
    (con B hB hd).ext c v ∈ (attachStage X m con (card c + 1)).obj
      (op (cone B (card (WithInitial.of ⦋0⦌ ⊗ c)))) := by
  induction hcard : card c using Nat.strong_induction_on generalizing c v with
  | _ k ih =>
    subst hcard
    have hB0 : 0 < B.dimension := by omega
    by_cases hv : v ∈ (coreFiltration (B.dimension - 1) X).obj (op (cone B (card c)))
    · refine Or.inl ?_
      have := (con B hB hd).ext_mem_coreFiltration c hv
      rwa [hd] at this
    by_cases hnd : EZCategory.IsNondegenerate X v
    · rcases (con B hB hd).isFree_or_exists_isFree hB0 hv hnd with hfree | ⟨c', θ, w, hθ, hw, rfl⟩
      · exact top_mem_attachStage ⟨B, hB, hrep, hd, c, v, hfree⟩ (n := card c + 1)
          (Nat.lt_succ_self _)
      · have hcθ : card c = card c' + 1 := by
          have h₁ := Fintype.card_le_of_injective _ (injective_toFun_of_isIso θ)
          have h₂ := Fintype.card_le_of_surjective _ (surjective_toFun_of_isIso θ)
          have h₃ := card_tensorObj (WithInitial.of ⦋0⦌) c'
          change _ = 1 + _ at h₃
          simp only [Fintype.card_fin] at h₁ h₂
          omega
        rw [← (con B hB hd).map_coneHom_whiskerLeft_ext, ← (con B hB hd).map_coneHom_zeroMul_ext,
          ← Functor.map_comp_apply, ← op_comp]
        exact map_top_mem_attachStage ⟨B, hB, hrep, hd, c', w, hw⟩ _
          (by change card c' < card c + 1; omega)
    · obtain ⟨c', σ, u, hcard, rfl⟩ := exists_card_lt_map_coneHom_eq hB0 hv hnd
      rw [← (con B hB hd).map_coneHom_whiskerLeft_ext]
      exact (attachStage X m con _).map _
        (attachStage_mono (by omega) _ (ih (card c') hcard c' u rfl))

namespace FreeCell

variable (P : FreeCell X m con)

theorem coneCoord_faceTop :
    coneCoord P.core _ P.faceTop = ((P.core.top : WithBot P.core.ogp),
      Finset.univ.image (toFun (inr (WithInitial.of ⦋0⦌) P.deg))) := by
  have h := coneCoord_coneHom P.core (toOrderHom (inr (WithInitial.of ⦋0⦌) P.deg))
    ((cone P.core (card P.deg)).top : WithBot _)
  rw [WithBot.map_coe, coneCoord_top] at h
  exact h

theorem faceTop_covBy : P.faceTop ⋖ P.atom.top := by
  refine GradeOrder.covBy_of_le_of_grade_eq_add_one (P.atom.le_top _) ?_
  have h₁ := grade_cone_add_one P.core _ P.atom.top
  have h₂ := grade_cone_add_one P.core _ P.faceTop
  rw [coneCoord_top] at h₁
  rw [coneCoord_faceTop, Finset.card_image_of_injective _ (injective_toFun_inr_zero P.deg),
    Finset.card_fin] at h₂
  rw [Finset.card_fin] at h₁
  have hc := card_tensorObj (WithInitial.of ⦋0⦌) P.deg
  change _ = 1 + _ at hc
  dsimp only at h₁ h₂
  omega

def hornSet : LowerSet P.atom.ogp :=
  hornSubset (atomicHornDataOfCovBy P.atom P.faceTop P.faceTop_covBy).toHornData

theorem mem_hornSet_iff {z : P.atom.ogp} : z ∈ P.hornSet ↔ z ≠ P.atom.top ∧ z ≠ P.faceTop :=
  mem_hornSet_closure_singleton_iff _ rfl

theorem map_top_mem_attachStage_of_mem_hornSet (h2 : 2 ≤ m) {U : Atom} (f : U ⟶ P.atom)
    (hf : f U.top ∈ P.hornSet) :
    X.map f.op P.top ∈ (attachStage X m con (card P.deg)).obj (op U) := by
  rw [P.mem_hornSet_iff] at hf
  obtain ⟨hne_top, hne_face⟩ := hf
  set z := f U.top with hz
  have hc := card_tensorObj (WithInitial.of ⦋0⦌) P.deg
  change _ = 1 + _ at hc
  by_cases hb : (coneCoord P.core _ (z : WithBot P.atom.ogp)).1 = P.core.top
  · have hS : ∃ k : Fin (card P.deg), toFun (inr (WithInitial.of ⦋0⦌) P.deg) k ∉
        (coneCoord P.core _ (z : WithBot P.atom.ogp)).2 := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      by_cases h0 : (⟨0, by omega⟩ : Fin (card (WithInitial.of ⦋0⦌ ⊗ P.deg))) ∈
          (coneCoord P.core _ (z : WithBot P.atom.ogp)).2
      · refine hne_top (eq_of_coneCoord_eq ((Prod.ext hb ?_).trans (coneCoord_top _ _).symm))
        refine Finset.eq_univ_of_forall fun i => ?_
        rcases Nat.eq_zero_or_pos i.val with hi | hi
        · exact (Fin.ext hi : i = ⟨0, by omega⟩) ▸ h0
        · have := hall ⟨i.val - 1, by omega⟩
          rwa [show toFun (inr (WithInitial.of ⦋0⦌) P.deg) ⟨i.val - 1, by omega⟩ = i from
            Fin.ext (by rw [val_toFun_inr_zero]; change i.val - 1 + 1 = i.val; omega)] at this
      · refine hne_face (eq_of_coneCoord_eq ((Prod.ext hb ?_).trans P.coneCoord_faceTop.symm))
        refine Finset.Subset.antisymm (fun i hi => ?_) fun i hi => ?_
        · have hi0 : 0 < i.val := Nat.pos_of_ne_zero fun h =>
            h0 ((Fin.ext h : i = ⟨0, by omega⟩) ▸ hi)
          exact Finset.mem_image.2 ⟨⟨i.val - 1, by omega⟩, Finset.mem_univ _,
            Fin.ext (by rw [val_toFun_inr_zero]; change i.val - 1 + 1 = i.val; omega)⟩
        · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hi
          exact hall k
    obtain ⟨k, hk⟩ := hS
    obtain ⟨d', δ, hδ, himδ⟩ := exists_injective_image_eq P.deg (Finset.univ.erase k)
    have hS' : (coneCoord P.core _ (z : WithBot P.atom.ogp)).2 ⊆
        Finset.univ.image (toOrderHom (WithInitial.of ⦋0⦌ ◁ δ)) := by
      intro i hi
      refine Finset.mem_image.2 ?_
      rcases Nat.eq_zero_or_pos i.val with hi0 | hi0
      · have hpos : 0 < card (WithInitial.of ⦋0⦌ ⊗ d') := by
          rw [card_tensorObj]
          change 0 < 1 + _
          omega
        exact ⟨⟨0, hpos⟩, Finset.mem_univ _, Fin.ext
          ((AugmentedSimplexCategory.val_toFun_whiskerLeft_of_eq_zero δ _ rfl).trans hi0.symm)⟩
      · have hik : (⟨i.val - 1, by omega⟩ : Fin (card P.deg)) ∈ Finset.univ.image (toFun δ) := by
          rw [himδ, Finset.mem_erase]
          refine ⟨fun hek => hk ?_, Finset.mem_univ _⟩
          rw [← hek]
          convert hi using 1
          exact Fin.ext (by rw [val_toFun_inr_zero]; change i.val - 1 + 1 = i.val; omega)
        obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hik
        have hj1 : j.val + 1 < card (WithInitial.of ⦋0⦌ ⊗ d') := by
          rw [card_tensorObj]
          change _ < 1 + _
          omega
        refine ⟨⟨j.val + 1, hj1⟩, Finset.mem_univ _, Fin.ext ?_⟩
        change (toFun (WithInitial.of ⦋0⦌ ◁ δ) ⟨j.val + 1, hj1⟩).val = i.val
        rw [val_toFun_whiskerLeft_of_ne_zero δ _ (Nat.succ_ne_zero _)]
        have := congrArg Fin.val hj
        change _ = i.val - 1 at this
        simp only [Nat.add_sub_cancel, Fin.eta]
        omega
    obtain ⟨g, rfl⟩ := exists_comp_coneHom_eq f
      (injective_toFun_whiskerLeft_zero δ hδ) hS'
    have hd' : card d' + 1 ≤ card P.deg := by
      have h₁ := Finset.card_image_of_injective (Finset.univ : Finset (Fin (card d'))) hδ
      rw [himδ, Finset.card_erase_of_mem (Finset.mem_univ _)] at h₁
      simp only [Finset.card_univ, Fintype.card_fin] at h₁
      have := k.isLt
      omega
    rw [op_comp, Functor.map_comp_apply]
    unfold FreeCell.top
    rw [P.contraction.map_coneHom_whiskerLeft_ext]
    exact (attachStage X m con _).map g.op (attachStage_mono hd' _
      (ext_mem_attachStage P.isCore P.isoRep_eq P.dimension_eq h2 d' _))
  · refine Or.inl ?_
    revert hb
    rcases hbz : (coneCoord P.core _ (z : WithBot P.atom.ogp)).1 with _ | b' <;> intro hb
    · obtain ⟨g, rfl⟩ := exists_comp_coneMap_eq (outputVertex P.core)
        (isInclusionHom_outputVertex P.core) f fun c hc =>
          absurd (hbz.symm.trans hc) WithBot.bot_ne_coe
      exact ⟨atomPoint, _, g, _, by rw [dimension_atomPoint]; exact Nat.zero_le _,
        (Functor.map_comp_apply X (coneMap (outputVertex P.core) _).op g.op _).symm⟩
    · have hb'' : b' ≠ P.core.top := fun h => hb (by rw [h]; rfl)
      obtain ⟨g, rfl⟩ := exists_comp_coneMap_eq (Atom.closureIncl P.core b')
        (Atom.isInclusionHom_closureIncl _ _) f fun c hc => by
          rw [Atom.closureIncl_top]
          exact (WithBot.coe_inj.1 (hbz.symm.trans hc)).symm.le
      refine ⟨Atom.ofClosure P.core b', _, g, _, ?_,
        (Functor.map_comp_apply X (coneMap (Atom.closureIncl P.core b') _).op g.op _).symm⟩
      have hlt := grade_strictMono (𝕆 := ℕ) (lt_of_le_of_ne (P.core.le_top b') hb'')
      rw [Atom.dimension_ofClosure]
      rw [← P.core.dimension_eq, P.dimension_eq] at hlt
      omega

theorem isCollapseHom_or_exists_of_notMem_hornSet {U : Atom} (f : U ⟶ P.atom)
    (hf : f U.top ∉ P.hornSet) :
    IsCollapseHom f ∨ ∃ g : U ⟶ cone P.core (card P.deg), IsCollapseHom g ∧
      g ≫ coneHom P.core (toOrderHom (inr (WithInitial.of ⦋0⦌) P.deg)) = f := by
  rw [P.mem_hornSet_iff, not_and_or, not_not, not_not] at hf
  rcases hf with htop | hface
  · exact Or.inl (isCollapseHom_of_apply_eq_top f htop)
  · refine Or.inr ?_
    obtain ⟨g, rfl⟩ := exists_comp_coneHom_eq f (σ := toOrderHom (inr (WithInitial.of ⦋0⦌) P.deg))
      (injective_toFun_inr_zero P.deg) (by
        have h : coneCoord P.core (card (WithInitial.of ⦋0⦌ ⊗ P.deg))
              (f U.top : WithBot (cone P.core (card (WithInitial.of ⦋0⦌ ⊗ P.deg))).ogp) =
            coneCoord P.core (card (WithInitial.of ⦋0⦌ ⊗ P.deg))
              (P.faceTop :
                WithBot (cone P.core (card (WithInitial.of ⦋0⦌ ⊗ P.deg))).ogp) := by
          rw [hface]
        rw [P.coneCoord_faceTop] at h
        rw [congrArg Prod.snd h]
        exact subset_rfl)
    have hinj := isInclusionHom_coneHom P.core
      (σ := toOrderHom (inr (WithInitial.of ⦋0⦌) P.deg)) (injective_toFun_inr_zero P.deg)
    exact ⟨g, isCollapseHom_of_apply_eq_top g (t := U.top) (hinj hface), rfl⟩

end FreeCell

theorem mem_or_exists_of_isNondegenerate_mem_attachStage (h2 : 2 ≤ m) {n : ℕ} {V : Atom}
    {w : X.obj (op V)} (hw : w ∈ (attachStage X m con n).obj (op V))
    (hnd : EZCategory.IsNondegenerate X w) :
    w ∈ (coreFiltration (m - 1) X).obj (op V) ∨ ∃ P : FreeCell X m con, card P.deg < n ∧
      ((∃ e : V ≅ P.atom, X.map e.hom.op P.top = w) ∨
        ∃ e : V ≅ cone P.core (card P.deg), X.map e.hom.op P.cell = w) := by
  induction n using Nat.strong_induction_on generalizing V w with
  | _ n ih =>
    rcases hw with hw | ⟨P, f, hP, rfl⟩
    · exact Or.inl hw
    obtain ⟨V₁, p, i, hp, hi, rfl⟩ := EZCategory.exists_factorization f
    have hpi : IsIso p := hnd p hp ⟨X.map i.op P.top, by rw [← Functor.map_comp_apply, ← op_comp]⟩
    have hf : IsInclusionHom (p ≫ i) := isInclusionHom_of_mono _
    by_cases hz : (p ≫ i) V.top ∈ P.hornSet
    · rcases ih _ hP (P.map_top_mem_attachStage_of_mem_hornSet h2 _ hz) hnd with h | ⟨P', hP', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨P', by omega, h⟩
    · rcases P.isCollapseHom_or_exists_of_notMem_hornSet _ hz with hc | ⟨g, hg, hgf⟩
      · have := isIso_of_isInclusionHom_of_isCollapseHom _ hf hc
        exact Or.inr ⟨P, hP, Or.inl ⟨asIso (p ≫ i), rfl⟩⟩
      · have hgi : IsInclusionHom g := fun a b hab => hf (by
          rw [← hgf, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hab])
        have := isIso_of_isInclusionHom_of_isCollapseHom g hgi hg
        refine Or.inr ⟨P, hP, Or.inr ⟨asIso g, ?_⟩⟩
        rw [← hgf, op_comp, Functor.map_comp_apply, P.map_coneHom_inr_top]
        rfl

theorem FreeCell.isNondegenerate_top (h2 : 2 ≤ m) (P : FreeCell X m con) :
    EZCategory.IsNondegenerate X P.top :=
  P.contraction.isNondegenerate_ext (by rw [P.dimension_eq]; omega) P.isFree

theorem FreeCell.top_notMem (P : FreeCell X m con) :
    P.top ∉ (coreFiltration (m - 1) X).obj (op P.atom) := by
  have := P.contraction.ext_not_mem P.isFree.not_mem
  rwa [P.dimension_eq] at this

theorem FreeCell.cell_notMem (P : FreeCell X m con) :
    P.cell ∉ (coreFiltration (m - 1) X).obj (op (cone P.core (card P.deg))) := by
  have := P.isFree.not_mem
  rwa [P.dimension_eq] at this

theorem mem_attachStage_of_map_mem {n : ℕ} {U V : Atom} (q : U ⟶ V) (hq : IsCollapseHom q)
    {r : X.obj (op V)} (h : X.map q.op r ∈ (attachStage X m con n).obj (op U)) :
    r ∈ (attachStage X m con n).obj (op V) := by
  have := isSplitEpi_of_isCollapseHom q hq
  have h' : X.map (section_ q).op (X.map q.op r) ∈ (attachStage X m con n).obj (op V) :=
    (attachStage X m con n).map (section_ q).op h
  rwa [← Functor.map_comp_apply, ← op_comp, IsSplitEpi.id, op_id, Functor.map_id_apply] at h'

theorem FreeCell.map_top_notMem_attachStage (h2 : 2 ≤ m) (P : FreeCell X m con) {n : ℕ}
    (hn : n ≤ card P.deg) {U : Atom} (f : U ⟶ P.atom)
    (hf : f U.top ∉ P.hornSet) :
    X.map f.op P.top ∉ (attachStage X m con n).obj (op U) := by
  intro hmem
  have hc := card_tensorObj (WithInitial.of ⦋0⦌) P.deg
  change _ = 1 + _ at hc
  rcases P.isCollapseHom_or_exists_of_notMem_hornSet f hf with hq | ⟨g, hg, rfl⟩
  · have hr := mem_attachStage_of_map_mem f hq hmem
    rcases mem_or_exists_of_isNondegenerate_mem_attachStage h2 hr (P.isNondegenerate_top h2) with
      h | ⟨P', hP', ⟨e, -⟩ | ⟨e, -⟩⟩
    · exact P.top_notMem h
    · have := (eq_and_nonempty_iso_of_iso_cone P.isCore P'.isCore e).1
      have hc' := card_tensorObj (WithInitial.of ⦋0⦌) P'.deg
      change _ = 1 + _ at hc'
      omega
    · have := (eq_and_nonempty_iso_of_iso_cone P.isCore P'.isCore e).1
      omega
  · rw [op_comp, Functor.map_comp_apply, P.map_coneHom_inr_top] at hmem
    have hr := mem_attachStage_of_map_mem g hg hmem
    rcases mem_or_exists_of_isNondegenerate_mem_attachStage h2 hr P.isFree.isNondegenerate with
      h | ⟨P', hP', ⟨e, he⟩ | ⟨e, -⟩⟩
    · exact P.cell_notMem h
    · obtain ⟨hcard, ⟨eB⟩⟩ := eq_and_nonempty_iso_of_iso_cone P.isCore P'.isCore e
      obtain ⟨B', hB', hrep', hd', c', x', hx'⟩ := P'
      obtain rfl : B' = P.core := (eq_of_iso_of_isoRep_eq P.isoRep_eq hrep' eB).symm
      have hdeg : P.deg = WithInitial.of ⦋0⦌ ⊗ c' := AugmentedSimplexCategory.card_injective hcard
      have hθ : coneHom P.core (toOrderHom (eqToHom hdeg)) = e.hom := by
        have : IsIso (coneHom P.core (toOrderHom (eqToHom hdeg))) :=
          inferInstanceAs (IsIso ((augmentedCone P.core).map (eqToHom hdeg)))
        exact congrArg Iso.hom
          (Subsingleton.elim (asIso (coneHom P.core (toOrderHom (eqToHom hdeg)))) e)
      exact P.isFree.not_isExt ⟨c', eqToHom hdeg, x', inferInstance, by rw [hθ]; exact he⟩
    · have := (eq_and_nonempty_iso_of_iso_cone P.isCore P'.isCore e).1
      omega

theorem FreeCell.eq_of_map_top_eq (h2 : 2 ≤ m) (P P' : FreeCell X m con)
    (hdeg : card P.deg = card P'.deg) {U : Atom} (f : U ⟶ P.atom) (f' : U ⟶ P'.atom)
    (hf : f U.top ∉ P.hornSet)
    (hf' : f' U.top ∉ P'.hornSet)
    (h : X.map f.op P.top = X.map f'.op P'.top) : P = P' ∧ HEq f f' := by
  have hc := card_tensorObj (WithInitial.of ⦋0⦌) P.deg
  have hc' := card_tensorObj (WithInitial.of ⦋0⦌) P'.deg
  change _ = 1 + _ at hc hc'
  have hnd := P.isNondegenerate_top h2
  have hnd' := P'.isNondegenerate_top h2
  rcases P.isCollapseHom_or_exists_of_notMem_hornSet f hf with hq | ⟨g, hg, rfl⟩ <;>
    rcases P'.isCollapseHom_or_exists_of_notMem_hornSet f' hf' with hq' | ⟨g', hg', rfl⟩
  · obtain ⟨e, ⟨he, hew⟩, -⟩ := EZCategory.existsUnique_iso_of_isNondegenerate X f f' P.top P'.top
      (isSplitEpi_of_isCollapseHom f hq) hnd (isSplitEpi_of_isCollapseHom f' hq') hnd' h
    obtain ⟨-, ⟨eB⟩⟩ := eq_and_nonempty_iso_of_iso_cone P.isCore P'.isCore e
    obtain ⟨B, hB, hrep, hd, c, x, hx⟩ := P
    obtain ⟨B', hB', hrep', hd', c', x', hx'⟩ := P'
    obtain rfl : B = B' := eq_of_iso_of_isoRep_eq hrep hrep' eB
    obtain rfl : c = c' := AugmentedSimplexCategory.card_injective hdeg
    obtain rfl : e = CategoryTheory.Iso.refl _ := Subsingleton.elim _ _
    rw [Iso.refl_hom, Category.comp_id] at he
    rw [Iso.refl_hom, op_id, Functor.map_id_apply] at hew
    subst he
    have hxx : x = x' := by
      have h₁ := FreeCell.map_coneHom_inr_top ⟨B, hB, hrep, hd, c, x, hx⟩
      have h₂ := FreeCell.map_coneHom_inr_top ⟨B, hB', hrep', hd', c, x', hx'⟩
      change X.map _ ((con B hB hd).ext c x') = x' at h₂
      change X.map _ ((con B hB hd).ext c x) = x at h₁
      change (con B hB hd).ext c x' = (con B hB hd).ext c x at hew
      rw [← h₁, ← h₂, hew]
    subst hxx
    exact ⟨rfl, HEq.rfl⟩
  · obtain ⟨e, -, -⟩ := EZCategory.existsUnique_iso_of_isNondegenerate X f g' P.top P'.cell
      (isSplitEpi_of_isCollapseHom f hq) hnd (isSplitEpi_of_isCollapseHom g' hg')
      P'.isFree.isNondegenerate (by rw [h, op_comp, Functor.map_comp_apply, P'.map_coneHom_inr_top])
    have := (eq_and_nonempty_iso_of_iso_cone P.isCore P'.isCore e).1
    omega
  · obtain ⟨e, -, -⟩ := EZCategory.existsUnique_iso_of_isNondegenerate X g f' P.cell P'.top
      (isSplitEpi_of_isCollapseHom g hg) P.isFree.isNondegenerate
      (isSplitEpi_of_isCollapseHom f' hq') hnd'
      (by rw [← h, op_comp, Functor.map_comp_apply, P.map_coneHom_inr_top])
    have := (eq_and_nonempty_iso_of_iso_cone P.isCore P'.isCore e).1
    omega
  · rw [op_comp, Functor.map_comp_apply, op_comp, Functor.map_comp_apply, P.map_coneHom_inr_top,
      P'.map_coneHom_inr_top] at h
    obtain ⟨e, ⟨he, hew⟩, -⟩ := EZCategory.existsUnique_iso_of_isNondegenerate X g g' P.cell
      P'.cell (isSplitEpi_of_isCollapseHom g hg) P.isFree.isNondegenerate
      (isSplitEpi_of_isCollapseHom g' hg') P'.isFree.isNondegenerate h
    obtain ⟨-, ⟨eB⟩⟩ := eq_and_nonempty_iso_of_iso_cone P.isCore P'.isCore e
    obtain ⟨B, hB, hrep, hd, c, x, hx⟩ := P
    obtain ⟨B', hB', hrep', hd', c', x', hx'⟩ := P'
    obtain rfl : B = B' := eq_of_iso_of_isoRep_eq hrep hrep' eB
    obtain rfl : c = c' := AugmentedSimplexCategory.card_injective hdeg
    obtain rfl : e = CategoryTheory.Iso.refl _ := Subsingleton.elim _ _
    rw [Iso.refl_hom, Category.comp_id] at he
    rw [Iso.refl_hom, op_id, Functor.map_id_apply] at hew
    subst he hew
    exact ⟨rfl, HEq.rfl⟩

theorem exists_mem_attachStage (h2 : 2 ≤ m) {U : Atom} {z : X.obj (op U)}
    (hz : z ∈ (coreFiltration m X).obj (op U)) :
    ∃ n, z ∈ (attachStage X m con n).obj (op U) := by
  obtain ⟨V, q, r, hq, hr, rfl⟩ := EZCategory.exists_isNondegenerate X U z
  have hrm : r ∈ (coreFiltration m X).obj (op V) := by
    have h' : X.map (section_ q).op (X.map q.op r) ∈ (coreFiltration m X).obj (op V) :=
      (coreFiltration m X).map (section_ q).op hz
    rwa [← Functor.map_comp_apply, ← op_comp, IsSplitEpi.id, op_id, Functor.map_id_apply] at h'
  suffices hr' : ∃ n, r ∈ (attachStage X m con n).obj (op V) by
    obtain ⟨n, hn⟩ := hr'
    exact ⟨n, (attachStage X m con n).map q.op hn⟩
  obtain ⟨F, s, hF, hFm, ⟨e⟩⟩ := exists_isCore_iso_cone_of_isNondegenerate hrm hr
  have hre : X.map e.hom.op (X.map e.inv.op r) = r := by
    rw [← Functor.map_comp_apply, ← op_comp, e.hom_inv_id, op_id, Functor.map_id_apply]
  by_cases hlt : F.dimension < m
  · exact ⟨0, Or.inl ⟨F, s, e.hom, X.map e.inv.op r, by omega, hre⟩⟩
  obtain ⟨eB⟩ := nonempty_iso_isoRep F
  have hB : IsCore (isoRep F) := IsCore.of_iso hF eB.symm
  have hd : (isoRep F).dimension = m := by
    rw [Atom.dimension_eq_of_iso eB]
    omega
  let e' : V ≅ cone (isoRep F) s := e ≪≫ (coneFunctor s).mapIso eB.symm
  obtain ⟨c, rfl⟩ := AugmentedSimplexCategory.exists_card_eq s
  have hre' : X.map e'.hom.op (X.map e'.inv.op r) = r := by
    rw [← Functor.map_comp_apply, ← op_comp, e'.hom_inv_id, op_id, Functor.map_id_apply]
  have hnd := isNondegenerate_map_hom e'.symm hr
  by_cases hY : X.map e'.inv.op r ∈
      (coreFiltration ((isoRep F).dimension - 1) X).obj (op (cone (isoRep F) (card c)))
  · rw [hd] at hY
    rw [← hre']
    exact ⟨0, Or.inl ((coreFiltration (m - 1) X).map e'.hom.op hY)⟩
  rcases (con (isoRep F) hB hd).isFree_or_exists_isFree (by omega) hY hnd with
    hfree | ⟨c', θ, w, -, hw, hθw⟩
  · let P : FreeCell X m con := ⟨isoRep F, hB, isoRep_isoRep F, hd, c, _, hfree⟩
    refine ⟨card c + 1, ?_⟩
    rw [← hre', show X.map e'.inv.op r = P.cell from rfl, ← P.map_coneHom_inr_top,
      ← Functor.map_comp_apply, ← op_comp]
    exact map_top_mem_attachStage P _ (Nat.lt_succ_self _)
  · let P : FreeCell X m con := ⟨isoRep F, hB, isoRep_isoRep F, hd, c', w, hw⟩
    refine ⟨card c' + 1, ?_⟩
    rw [← hre', ← hθw, ← Functor.map_comp_apply, ← op_comp]
    exact map_top_mem_attachStage P _ (Nat.lt_succ_self _)

theorem FreeCell.boundary_closure_faceTop_zero (P : FreeCell X m con) (hP : 1 ≤ card P.deg)
    (α : Bool) :
    P.atom.ogp.boundary (.Iic P.faceTop) 0 α = P.atom.ogp.boundary ⊤ 0 α := by
  rw [← P.atom.Iic_top]
  have hc := card_tensorObj (WithInitial.of ⦋0⦌) P.deg
  change _ = 1 + _ at hc
  cases α
  · refine SetLike.coe_injective ?_
    change ((P.atom.ogp.boundary (.Iic (coneHom P.core (toOrderHom (inr (WithInitial.of ⦋0⦌)
      P.deg)) (cone P.core (card P.deg)).top)) 0 false : Set P.atom.ogp)) = _
    rw [← (Atom.isMap
        (coneHom P.core (toOrderHom (inr (WithInitial.of ⦋0⦌) P.deg)))).image_boundary,
      boundary_closure_top_zero_false_cone, Set.image_image, boundary_closure_top_zero_false_cone]
    exact congrArg (fun g : P.core ⟶ P.atom =>
      g '' (P.core.ogp.boundary (.Iic P.core.top) 0 false : Set P.core.ogp))
      (coneIncl_comp_coneHom _ _)
  · have hS : (coneCoord P.core _ (P.faceTop : WithBot P.atom.ogp)).2.Nonempty := by
      rw [P.coneCoord_faceTop]
      exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, by omega⟩)⟩
    have hT : (coneCoord P.core _ (P.atom.top : WithBot P.atom.ogp)).2.Nonempty := by
      rw [coneCoord_top]
      exact Finset.univ_nonempty_iff.2 ⟨⟨0, by omega⟩⟩
    refine boundary_closure_zero_true_eq_of_max'_eq hS hT (le_antisymm ?_ ?_)
    · exact Finset.max'_subset hS fun i _ => by
        rw [coneCoord_top]
        exact Finset.mem_univ i
    · refine (Finset.max'_le _ hT _ fun i _ => ?_).trans (Finset.le_max' _
        (toFun (inr (WithInitial.of ⦋0⦌) P.deg) ⟨card P.deg - 1, by omega⟩) ?_)
      · rw [Fin.le_iff_val_le_val, val_toFun_inr_zero]
        have := i.isLt
        change _ ≤ card P.deg - 1 + 1
        omega
      · rw [P.coneCoord_faceTop]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

end Stages

section Glue

variable {Y E : DiagSet.{u}} (G : Subfunctor Y) {J : Type w} (A : J → DiagSet.{u})
  (a : ∀ j, A j ⟶ Y)
  (φ : ∀ j, A j ⟶ E)
  (hcov : ∀ (U : Atom) (z : Y.obj (op U)), z ∈ G.obj (op U) → ∃ j y, (a j).app (op U) y = z)
  (hcomp : ∀ (U : Atom) (j k : J) (y : (A j).obj (op U)) (y' : (A k).obj (op U)),
    (a j).app (op U) y = (a k).app (op U) y' → (φ j).app (op U) y = (φ k).app (op U) y')

private noncomputable def glueFun {U : Atom} (z : Y.obj (op U)) (hz : z ∈ G.obj (op U)) :
    E.obj (op U) :=
  (φ (hcov U z hz).choose).app (op U) (hcov U z hz).choose_spec.choose

include hcomp in
private theorem glueFun_eq {U : Atom} (z : Y.obj (op U)) (hz : z ∈ G.obj (op U)) (j : J)
    (y : (A j).obj (op U)) (hy : (a j).app (op U) y = z) :
    glueFun G A a φ hcov z hz = (φ j).app (op U) y :=
  hcomp U _ _ _ _ ((hcov U z hz).choose_spec.choose_spec.trans hy.symm)

private noncomputable def glue : G.toFunctor ⟶ E where
  app U := TypeCat.ofHom fun z => glueFun G A a φ hcov z.1 z.2
  naturality U U' h := by
    ext z
    obtain ⟨j, y, hy⟩ := hcov _ z.1 z.2
    have h₁ : (a j).app U' ((A j).map h y) = Y.map h z.1 := by
      rw [← hy]
      exact NatTrans.naturality_apply (a j) h y
    have h₂ := glueFun_eq G A a φ hcov hcomp (Y.map h z.1) (G.toFunctor.map h z).2 j _ h₁
    have h₃ := glueFun_eq G A a φ hcov hcomp z.1 z.2 j y hy
    exact h₂.trans ((NatTrans.naturality_apply (φ j) h y).trans (congrArg (E.map h) h₃.symm))

include hcomp in
private theorem glue_app {U : Atom} (z : G.toFunctor.obj (op U)) (j : J)
    (y : (A j).obj (op U)) (hy : (a j).app (op U) y = z.1) :
    (glue G A a φ hcov hcomp).app (op U) z = (φ j).app (op U) y :=
  glueFun_eq G A a φ hcov hcomp z.1 z.2 j y hy

end Glue

section Lift

variable {X : DiagSet.{u}} {E F : MarkedDiagSet.{u}} (p : E ⟶ F)
  (b : (MarkedDiagSet.markedAboveFunctor 1).obj X ⟶ F)

theorem map_mem_marked_markedAbove {U : Atom} {x : X.obj (op U)}
    (hx : IsDegenerate X x ∨ 1 < U.dimension) :
    (Homotopical.MarkedPresheaf.forget.map b).app (op U) x ∈ F.marked U :=
  Homotopical.MarkedPresheaf.map_mem_marked b
    ((Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ U x).2 hx)

structure PartialLift (W : Subfunctor X) where
  map : W.toFunctor ⟶ E.underlying
  map_mem_marked (U : Atom) (z : W.toFunctor.obj (op U)) :
    IsDegenerate X z.1 ∨ 1 < U.dimension → map.app (op U) z ∈ E.marked U
  map_comp : map ≫ Homotopical.MarkedPresheaf.forget.map p =
    W.ι ≫ Homotopical.MarkedPresheaf.forget.map b

variable {p b}

theorem PartialLift.map_app_comp {W : Subfunctor X} (φ : PartialLift p b W) {U : Atom}
    (z : W.toFunctor.obj (op U)) :
    (Homotopical.MarkedPresheaf.forget.map p).app (op U) (φ.map.app (op U) z) =
      (Homotopical.MarkedPresheaf.forget.map b).app (op U) z.1 :=
  ConcreteCategory.congr_hom (NatTrans.congr_app φ.map_comp (op U)) z

theorem mem_marked_markedClosedSubset_univ {V : Atom} {A' : Set V.ogp}
    (hA : ∀ a ∈ A', a ∈ (⊤ : LowerSet V.ogp) ∧ 0 < grade ℕ a)
    (hA' : ∀ a, 1 < grade ℕ a → a ∈ A') {U : Atom}
    (f : (closedSubpresheaf.{u} V ⊤).toFunctor.obj (op U))
    (hf : IsDegenerate (ball V) f.1 ∨ 1 < U.dimension) :
    f ∈ (markedClosedSubset V ⊤ A' hA).marked U := by
  refine (mem_marked_markedClosedSubset_univ_iff V A' hA f).2 ?_
  by_cases hd : IsDegenerate (ball V) f.1
  · exact Or.inl hd
  refine Or.inr (hA' _ ?_)
  obtain ⟨V₁, q, i, hq, hi, hqi⟩ := EZCategory.exists_factorization f.1.down
  have hqiso : IsIso q := by
    by_contra hni
    exact hd ⟨V₁, q, ⟨i⟩, isCollapseHom_of_isSplitEpi q, hni, congrArg ULift.up hqi⟩
  have hinc : IsInclusionHom f.1.down := by
    rw [← hqi]
    exact isInclusionHom_of_mono _
  have hg : grade ℕ (ConcreteCategory.hom f.1.down U.top) = U.dimension :=
    (grade_eq_of_isInclusionHom _ hinc U.top).trans U.dimension_eq.symm
  rw [hg]
  exact hf.resolve_left hd

end Lift

section Attach

variable {X : DiagSet.{u}} {m : ℕ}
  {con : ∀ B : Atom, IsCore B → B.dimension = m → CoherentContraction B X}
  {E F : MarkedDiagSet.{u}} {p : E ⟶ F} {b : (MarkedDiagSet.markedAboveFunctor 1).obj X ⟶ F}

theorem CoherentContraction.isDegenerate_map_ext_star {B : Atom} (C : CoherentContraction B X)
    (x : X.obj (op B)) {V : Atom} (g : V ⟶ cone B 1) (hg : g V.top ≤ coneOneEdge B)
    (hV : 0 < V.dimension) :
    IsDegenerate X (X.map g.op (C.ext WithInitial.star x)) := by
  obtain ⟨g', rfl⟩ := exists_comp_coneMap_eq (outputVertex B) (isInclusionHom_outputVertex B) g
    fun c hc => by
      have h := (le_iff_coneCoord.1 hg).1
      rw [hc, coneCoord_coneOneEdge] at h
      rw [outputVertex_apply]
      exact WithBot.coe_le_coe.1 h
  have he := C.map_coneMap_outputVertex x
  refine ⟨atomPoint, toAtomPoint V, X.map (outputVertex B).op x, isCollapseHom_toAtomPoint V,
    fun hiso => ?_, ?_⟩
  · have := Atom.dimension_eq_of_iso (asIso (toAtomPoint V))
    rw [dimension_atomPoint] at this
    omega
  · exact ((congrArg (fun f : V ⟶ atomPoint => X.map f.op (X.map (outputVertex B).op x))
      (Subsingleton.elim (toAtomPoint V) (g' ≫ toAtomPoint (cone atomPoint 1)))).trans
      (Functor.map_comp_apply X (toAtomPoint (cone atomPoint 1)).op g'.op _)).trans
      ((congrArg (X.map g'.op) he.symm).trans
        (Functor.map_comp_apply X (coneMap (outputVertex B) 1).op g'.op _).symm)

namespace FreeCell

variable (h2 : 2 ≤ m) (P : FreeCell X m con)

def hornToStage {n : ℕ} (hn : card P.deg ≤ n) :
    (closedSubpresheaf P.atom (P.hornSet)).toFunctor ⟶
      (attachStage X m con n).toFunctor :=
  Subfunctor.lift ((closedSubpresheaf _ _).ι ≫ uliftYonedaEquiv.symm P.top) (by
    rintro ⟨U⟩ _ ⟨z, rfl⟩
    exact attachStage_mono hn _
      (P.map_top_mem_attachStage_of_mem_hornSet h2 z.1.down (z.2 U.top)))

theorem mem_closedSubpresheaf_hornSet {U : Atom} (f : U ⟶ P.atom)
    (hf : f U.top ∈ P.hornSet) :
    ULift.up f ∈ (closedSubpresheaf.{u} P.atom
      (P.hornSet)).obj (op U) := by
  intro t
  rw [P.mem_hornSet_iff] at hf ⊢
  have hle := (Atom.isMap f).monotone (U.le_top t)
  refine ⟨fun h => hf.1 (le_antisymm (P.atom.le_top _) (h ▸ hle)), fun h => ?_⟩
  rw [h] at hle
  exact P.faceTop_covBy.2 (lt_of_le_of_ne hle (Ne.symm hf.2))
    (lt_of_le_of_ne (P.atom.le_top _) hf.1)

include h2 in
theorem isDegenerate_of_notMem_hornSet {U : Atom} (f : U ⟶ P.atom)
    (hf : f U.top ∉ P.hornSet)
    (hdeg : IsDegenerate X (X.map f.op P.top)) : IsDegenerate (ball.{u} P.atom) (ULift.up f) := by
  rcases P.isCollapseHom_or_exists_of_notMem_hornSet f hf with hq | ⟨g, hg, rfl⟩
  · by_cases hiso : IsIso f
    · exact absurd (isNondegenerate_map_hom (asIso f) (P.isNondegenerate_top h2))
        ((isDegenerate_iff_not_isNondegenerate X _).1 hdeg)
    · exact ⟨P.atom, f, ⟨𝟙 _⟩, hq, hiso, congrArg ULift.up (Category.comp_id f)⟩
  · by_cases hiso : IsIso g
    · refine absurd (isNondegenerate_map_hom (asIso g) P.isFree.isNondegenerate)
        ((isDegenerate_iff_not_isNondegenerate X _).1 ?_)
      rw [op_comp, Functor.map_comp_apply, P.map_coneHom_inr_top] at hdeg
      exact hdeg
    · exact ⟨_, g, ⟨_⟩, hg, hiso, rfl⟩

structure IsLift {n : ℕ} (hn : card P.deg ≤ n) (φ : PartialLift p b (attachStage X m con n))
    (ψ : ball P.atom ⟶ E.underlying) : Prop where
  app_of_mem : ∀ {U : Atom}
    (z : (closedSubpresheaf P.atom
      (P.hornSet)).toFunctor.obj (op U)),
    ψ.app (op U) z.1 = φ.map.app (op U) ((P.hornToStage h2 hn).app (op U) z)
  comp : ψ ≫ Homotopical.MarkedPresheaf.forget.map p =
    uliftYonedaEquiv.symm P.top ≫ Homotopical.MarkedPresheaf.forget.map b
  mem_marked : ∀ {U : Atom} (f : U ⟶ P.atom),
    IsDegenerate (ball.{u} P.atom) (ULift.up f) ∨ 1 < U.dimension → ψ.app (op U) ⟨f⟩ ∈ E.marked U

theorem exists_isLift_of_pos
    (hp : fibrations (MarkedDiagSet.Coinductive 1) ((MarkedDiagSet.toCoinductive 1).map p))
    (hP : 1 ≤ card P.deg)
    {n : ℕ} (hn : card P.deg ≤ n) (φ : PartialLift p b (attachStage X m con n)) :
    ∃ ψ, P.IsLift h2 hn φ ψ := by
  let H := atomicHornDataOfCovBy P.atom P.faceTop P.faceTop_covBy
  obtain ⟨mh, ⟨e⟩⟩ := exists_markedHornData_iso_markedAbove_hornInclusion H P.faceTop rfl
    (P.boundary_closure_faceTop_zero hP)
  have hl : HasLiftingProperty (markedHornInclusion mh) p :=
    hasLiftingProperty_of_coinductiveGenerators 1
      ((le_sup_left.trans le_sup_left : markedHorns ≤ coinductiveGenerators 1) _
        (MorphismProperty.ofHoms.mk mh)) hp
  have hl' := HasLiftingProperty.of_arrow_iso_left e p
  let u := P.hornToStage h2 hn ≫ φ.map
  let top : (MarkedDiagSet.markedAboveFunctor 1).obj (horn H.toHornData) ⟶ E :=
    Homotopical.MarkedPresheaf.homMk (X := MarkedDiagSet.markedAbove _ 1) u fun V z hz =>
      φ.map_mem_marked V _ ((Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ V z).1 hz
        |>.imp_left fun hd => isDegenerate_app (P.hornToStage h2 hn ≫ (attachStage X m con _).ι) hd)
  let bot : (MarkedDiagSet.markedAboveFunctor 1).obj (ball P.atom) ⟶ F :=
    Homotopical.MarkedPresheaf.homMk (X := MarkedDiagSet.markedAbove _ 1)
      (uliftYonedaEquiv.symm P.top ≫ Homotopical.MarkedPresheaf.forget.map b) fun V z hz =>
        map_mem_marked_markedAbove b ((Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ V z).1 hz
          |>.imp_left fun hd => isDegenerate_app (uliftYonedaEquiv.symm P.top) hd)
  have sq : CommSq top ((MarkedDiagSet.markedAboveFunctor 1).map (hornInclusion H.toHornData))
      p bot := ⟨Homotopical.MarkedPresheaf.hom_ext (by
    ext ⟨U⟩ z
    exact φ.map_app_comp ((P.hornToStage h2 hn).app (op U) z))⟩
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (hl'.sq_hasLift sq).exists_lift
  refine ⟨Homotopical.MarkedPresheaf.forget.map l, ⟨fun z => ?_, ?_, fun f hf => ?_⟩⟩
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg Homotopical.MarkedPresheaf.forget.map hl₁) _) z
  · exact congrArg Homotopical.MarkedPresheaf.forget.map hl₂
  · have hf' : ULift.up f ∈ (MarkedDiagSet.markedAbove (ball H.atom) 1).marked _ :=
      (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 hf
    exact Homotopical.MarkedPresheaf.map_mem_marked l hf'

theorem exists_isLift_of_zero
    (hp : fibrations (MarkedDiagSet.Coinductive 1) ((MarkedDiagSet.toCoinductive 1).map p))
    (hP : card P.deg = 0)
    {n : ℕ} (hn : card P.deg ≤ n) (φ : PartialLift p b (attachStage X m con n)) :
    ∃ ψ, P.IsLift h2 hn φ ψ := by
  obtain ⟨B, hB, hrep, hd, c, x, hx⟩ := P
  obtain rfl : c = WithInitial.star := AugmentedSimplexCategory.card_injective hP
  let P : FreeCell X m con := ⟨B, hB, hrep, hd, WithInitial.star, x, hx⟩
  have hB1 : 1 ≤ B.dimension := by omega
  let mh := coneOneMarkedHorn B hB1
  have hl : HasLiftingProperty (markedHornInclusion mh) p :=
    hasLiftingProperty_of_coinductiveGenerators 1
      ((le_sup_left.trans le_sup_left : markedHorns ≤ coinductiveGenerators 1) _
        (MorphismProperty.ofHoms.mk mh)) hp
  let C := con B hB hd
  have hcl : (cone B 1).dimension = B.dimension + 1 := dimension_cone B 1
  have htop : 1 < grade ℕ (cone B 1).top := by
    rw [← (cone B 1).dimension_eq, hcl]
    omega
  have hface : ∀ y, y ⋖ (cone B 1).top → 1 < grade ℕ y := by
    intro y hy
    have := Nat.covBy_iff_add_one_eq.1 (hy.grade ℕ)
    rw [← (cone B 1).dimension_eq, hcl] at this
    omega
  have hmarking : ∀ {V : Atom} (g : V ⟶ cone B 1) (a : (cone B 1).ogp),
      a ∈ mh.targetMarking → Atom.map g ⊤ = LowerSet.Iic a →
      V.dimension = grade ℕ a →
      IsDegenerate X (X.map g.op P.top) ∨ 1 < V.dimension := by
    intro V g a ha him hdim
    rcases mh.mem_targetMarking_iff.1 ha with h | ⟨-, h⟩ | ha
    · subst h
      rw [hdim]
      exact Or.inr htop
    · subst h
      rw [hdim]
      exact Or.inr (hface _ (coneOneBase_covBy B))
    · have ha' : a ∈ coneOneMarking B := ha
      rcases ha'.2 with h | h
      · exact Or.inr (hdim ▸ h)
      · subst h
        exact Or.inl (C.isDegenerate_map_ext_star x g (apply_top_eq_of_map_eq g him).le
          (by rw [hdim, grade_coneOneEdge]; omega))
  have hall : ∀ a, 1 < grade ℕ a → a ∈ mh.targetMarking := by
    have hmark : ∀ a, 1 < grade ℕ a → a ≠ (cone B 1).top → a ≠ coneOneBase B →
        a ∈ coneOneMarking B := fun a ha h₁ h₂ =>
      ⟨(mem_hornSet_closure_singleton_iff (coneOneHornData B).toHornData rfl).2 ⟨h₁, h₂⟩,
        Or.inl ha⟩
    intro a ha
    refine mh.mem_targetMarking_iff.2 ?_
    by_cases h₁ : a = (cone B 1).top
    · exact Or.inl h₁
    by_cases h₂ : a = coneOneBase B
    · refine Or.inr (Or.inl ⟨fun y hy => ?_, h₂⟩)
      obtain ⟨hcov, hor⟩ := hy
      have hside := mh.face_mem.2
      refine hmark y (hface y hcov) (ne_of_lt hcov.1) fun h => ?_
      subst h
      have hs : (!mh.side) = mh.side := hor.symm.trans hside
      cases mh.side <;> simp at hs
    · exact Or.inr (Or.inr (hmark a ha h₁ h₂))
  let u := P.hornToStage h2 hn ≫ φ.map
  let top : mh.source ⟶ E := Homotopical.MarkedPresheaf.homMk u fun V z hz => by
    refine φ.map_mem_marked V _ ?_
    rcases (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ V z).1 hz with hd' |
      ⟨a, ha, him, hdim⟩
    · exact Or.inl (isDegenerate_app (P.hornToStage h2 hn ≫ (attachStage X m con _).ι) hd')
    · exact hmarking z.1.down a (mh.mem_targetMarking_iff.2 (Or.inr (Or.inr ha))) him hdim
  let bot : mh.target ⟶ F := Homotopical.MarkedPresheaf.homMk
    ((closedSubpresheafUnivIso (cone B 1)).hom ≫ uliftYonedaEquiv.symm P.top ≫
      Homotopical.MarkedPresheaf.forget.map b) fun V z hz => by
    refine map_mem_marked_markedAbove b ?_
    rcases (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ V z).1 hz with hd' |
      ⟨a, ha, him, hdim⟩
    · exact Or.inl (isDegenerate_app ((closedSubpresheafUnivIso (cone B 1)).hom ≫
        uliftYonedaEquiv.symm P.top) hd')
    · exact hmarking z.1.down a ha him hdim
  have sq : CommSq top (markedHornInclusion mh) p bot :=
    ⟨Homotopical.MarkedPresheaf.hom_ext (by
      ext ⟨U⟩ z
      exact φ.map_app_comp ((P.hornToStage h2 hn).app (op U) z))⟩
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (hl.sq_hasLift sq).exists_lift
  refine ⟨(closedSubpresheafUnivIso (cone B 1)).inv ≫ Homotopical.MarkedPresheaf.forget.map l,
    ⟨fun z => ?_, ?_, fun f hf => ?_⟩⟩
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg Homotopical.MarkedPresheaf.forget.map hl₁) _) z
  · have h := congrArg Homotopical.MarkedPresheaf.forget.map hl₂
    rw [Functor.map_comp] at h
    refine (Category.assoc _ _ _).trans ((congrArg _ h).trans ?_)
    exact (closedSubpresheafUnivIso (cone B 1)).inv_hom_id_assoc
      (uliftYonedaEquiv.symm P.top ≫ Homotopical.MarkedPresheaf.forget.map b)
  · refine Homotopical.MarkedPresheaf.map_mem_marked l
      (mem_marked_markedClosedSubset_univ _ hall ⟨⟨f⟩, fun _ => LowerSet.mem_top⟩ hf)

theorem exists_isLift
    (hp : fibrations (MarkedDiagSet.Coinductive 1) ((MarkedDiagSet.toCoinductive 1).map p))
    {n : ℕ} (hn : card P.deg ≤ n)
    (φ : PartialLift p b (attachStage X m con n)) :
    ∃ ψ, P.IsLift h2 hn φ ψ := by
  rcases Nat.eq_zero_or_pos (card P.deg) with h | h
  · exact P.exists_isLift_of_zero h2 hp h hn φ
  · exact P.exists_isLift_of_pos h2 hp h hn φ

end FreeCell

theorem PartialLift.exists_attachStage_succ
    (hp : fibrations (MarkedDiagSet.Coinductive 1) ((MarkedDiagSet.toCoinductive 1).map p))
    (h2 : 2 ≤ m) {n : ℕ}
    (φ : PartialLift p b (attachStage X m con n)) :
    ∃ φ' : PartialLift p b (attachStage X m con (n + 1)), ∀ {U : Atom}
      (z : (attachStage X m con n).toFunctor.obj (op U)),
      φ'.map.app (op U) ⟨z.1, attachStage_mono n.le_succ _ z.2⟩ = φ.map.app (op U) z := by
  choose ψ hψ using fun P : {P : FreeCell X m con // card P.deg = n} =>
    P.1.exists_isLift h2 hp P.2.le φ
  let A : Option {P : FreeCell X m con // card P.deg = n} → DiagSet.{u} := fun
    | none => (attachStage X m con n).toFunctor
    | some P => ball P.1.atom
  let a : ∀ j, A j ⟶ X := fun
    | none => (attachStage X m con n).ι
    | some P => uliftYonedaEquiv.symm P.1.top
  let φj : ∀ j, A j ⟶ E.underlying := fun
    | none => φ.map
    | some P => ψ P
  have hstage : ∀ (U : Atom) j (y : (A j).obj (op U))
      (h : (a j).app (op U) y ∈ (attachStage X m con n).obj (op U)),
      (φj j).app (op U) y = φ.map.app (op U) ⟨_, h⟩ := by
    rintro U (_ | P) y h
    · rfl
    · by_cases hf : ConcreteCategory.hom y.down U.top ∈ P.1.hornSet
      · exact ((hψ P).app_of_mem ⟨y, P.1.mem_closedSubpresheaf_hornSet y.down hf⟩).trans rfl
      · exact absurd h (P.1.map_top_notMem_attachStage h2 P.2.ge y.down hf)
  have hcov : ∀ (U : Atom) (z : X.obj (op U)), z ∈ (attachStage X m con (n + 1)).obj (op U) →
      ∃ j y, (a j).app (op U) y = z := by
    rintro U z (hz | ⟨P, f, hP, rfl⟩)
    · exact ⟨none, ⟨z, Or.inl hz⟩, rfl⟩
    · rcases (Nat.lt_succ_iff.1 hP).lt_or_eq with hlt | heq
      · exact ⟨none, ⟨_, Or.inr ⟨P, f, hlt, rfl⟩⟩, rfl⟩
      · exact ⟨some ⟨P, heq⟩, ⟨f⟩, rfl⟩
  have hcomp : ∀ (U : Atom) j k (y : (A j).obj (op U)) (y' : (A k).obj (op U)),
      (a j).app (op U) y = (a k).app (op U) y' → (φj j).app (op U) y = (φj k).app (op U) y' := by
    intro U j k y y' h
    by_cases hz : (a j).app (op U) y ∈ (attachStage X m con n).obj (op U)
    · have hz' : (a k).app (op U) y' ∈ (attachStage X m con n).obj (op U) := h ▸ hz
      exact (hstage U j y hz).trans ((congrArg (φ.map.app (op U)) (Subtype.ext h)).trans
        (hstage U k y' hz').symm)
    have hnot : ∀ (P : {P : FreeCell X m con // card P.deg = n}) (f : U ⟶ P.1.atom),
        X.map f.op P.1.top ∉ (attachStage X m con n).obj (op U) →
        f U.top ∉ P.1.hornSet :=
      fun P f hn hf => hn (attachStage_mono P.2.le _
        (P.1.map_top_mem_attachStage_of_mem_hornSet h2 f hf))
    rcases j with _ | P
    · exact absurd y.2 hz
    rcases k with _ | P'
    · have hy' : (a none).app (op U) y' ∈ (attachStage X m con n).obj (op U) := y'.2
      rw [← h] at hy'
      exact absurd hy' hz
    have hz' : (a (some P')).app (op U) y' ∉ (attachStage X m con n).obj (op U) := h ▸ hz
    obtain ⟨y⟩ := y
    obtain ⟨y'⟩ := y'
    obtain ⟨hPP, hyy⟩ := P.1.eq_of_map_top_eq h2 P'.1 (P.2.trans P'.2.symm) y y'
      (hnot P y hz) (hnot P' y' hz') h
    obtain ⟨P, hP⟩ := P
    obtain ⟨P', hP'⟩ := P'
    subst hPP
    cases hyy
    rfl
  let g := glue (attachStage X m con (n + 1)) A a φj hcov hcomp
  have hg : ∀ {U : Atom} (z : (attachStage X m con (n + 1)).toFunctor.obj (op U)),
      ∃ j y, (a j).app (op U) y = z.1 ∧ g.app (op U) z = (φj j).app (op U) y := by
    intro U z
    obtain ⟨j, y, hy⟩ := hcov U z.1 z.2
    exact ⟨j, y, hy, glue_app _ _ _ _ _ hcomp z j y hy⟩
  refine ⟨⟨g, fun U z hz => ?_, ?_⟩, fun z => glue_app _ _ _ _ _ hcomp _ none z rfl⟩
  · obtain ⟨j, y, hy, hgz⟩ := hg z
    rw [hgz]
    rcases j with _ | P
    · have hy' : y.1 = z.1 := hy
      refine φ.map_mem_marked U y ?_
      rw [hy']
      exact hz
    · have hy' : X.map y.down.op P.1.top = z.1 := hy
      rw [← hy'] at hz
      by_cases hf : ConcreteCategory.hom y.down U.top ∈ P.1.hornSet
      · change (ψ P).app (op U) y ∈ E.marked U
        rw [(hψ P).app_of_mem ⟨y, P.1.mem_closedSubpresheaf_hornSet y.down hf⟩]
        exact φ.map_mem_marked U _ hz
      · exact (hψ P).mem_marked y.down
          (hz.imp_left (P.1.isDegenerate_of_notMem_hornSet h2 y.down hf))
  · ext ⟨U⟩ z
    obtain ⟨j, y, hy, hgz⟩ := hg z
    refine (congrArg ((Homotopical.MarkedPresheaf.forget.map p).app (op U)) hgz).trans ?_
    rcases j with _ | P
    · exact (φ.map_app_comp y).trans (congrArg _ hy)
    · exact (ConcreteCategory.congr_hom (NatTrans.congr_app (hψ P).comp (op U)) y).trans
        (congrArg ((Homotopical.MarkedPresheaf.forget.map b).app (op U)) hy)

end Attach

section Chain

variable {X : DiagSet.{u}} {E F : MarkedDiagSet.{u}} {p : E ⟶ F}
  {b : (MarkedDiagSet.markedAboveFunctor 1).obj X ⟶ F}

def PartialLift.ofLE {W W' : Subfunctor X} (h : W' ≤ W) (φ : PartialLift p b W) :
    PartialLift p b W' where
  map := Subfunctor.homOfLe h ≫ φ.map
  map_mem_marked U z hz := φ.map_mem_marked U ⟨z.1, h _ z.2⟩ hz
  map_comp := (Category.assoc _ _ _).trans ((congrArg _ φ.map_comp).trans rfl)

theorem PartialLift.exists_of_chain {W : ℕ → Subfunctor X} (hW : Monotone W)
    (φ : ∀ n, PartialLift p b (W n))
    (hφ : ∀ n {U : Atom} (z : (W n).toFunctor.obj (op U)),
      (φ (n + 1)).map.app (op U) ⟨z.1, hW n.le_succ _ z.2⟩ = (φ n).map.app (op U) z)
    (W' : Subfunctor X) (hle : ∀ n, W n ≤ W')
    (hW' : ∀ (U : Atom) (z : X.obj (op U)), z ∈ W'.obj (op U) → ∃ n, z ∈ (W n).obj (op U)) :
    ∃ ψ : PartialLift p b W', ∀ n {U : Atom} (z : (W n).toFunctor.obj (op U)),
      ψ.map.app (op U) ⟨z.1, hle n _ z.2⟩ = (φ n).map.app (op U) z := by
  have hmono : ∀ n k (hnk : n ≤ k) {U : Atom} (z : (W n).toFunctor.obj (op U)),
      (φ k).map.app (op U) ⟨z.1, hW hnk _ z.2⟩ = (φ n).map.app (op U) z := by
    intro n k hnk U z
    induction k, hnk using Nat.le_induction with
    | base => rfl
    | succ k hnk ih => exact (hφ k ⟨z.1, hW hnk _ z.2⟩).trans ih
  have hcov : ∀ (U : Atom) (z : X.obj (op U)), z ∈ W'.obj (op U) →
      ∃ (n : ℕ) (y : (W n).toFunctor.obj (op U)), (W n).ι.app (op U) y = z := by
    intro U z hz
    obtain ⟨n, hn⟩ := hW' U z hz
    exact ⟨n, ⟨z, hn⟩, rfl⟩
  have hcomp : ∀ (U : Atom) (j k : ℕ) (y : (W j).toFunctor.obj (op U))
      (y' : (W k).toFunctor.obj (op U)), (W j).ι.app (op U) y = (W k).ι.app (op U) y' →
      (φ j).map.app (op U) y = (φ k).map.app (op U) y' := by
    intro U j k y y' h
    rcases le_total j k with hjk | hkj
    · exact (hmono j k hjk y).symm.trans (congrArg _ (Subtype.ext h))
    · exact (congrArg _ (Subtype.ext h)).trans (hmono k j hkj y')
  let g := glue W' (fun n => (W n).toFunctor) (fun n => (W n).ι) (fun n => (φ n).map) hcov hcomp
  refine ⟨⟨g, fun U z hz => ?_, ?_⟩, fun n U z => glue_app _ _ _ _ _ hcomp _ n z rfl⟩
  · obtain ⟨n, y, hy⟩ := hcov U z.1 z.2
    rw [glue_app _ _ _ _ _ hcomp z n y hy]
    have hy' : y.1 = z.1 := hy
    refine (φ n).map_mem_marked U y ?_
    rw [hy']
    exact hz
  · ext ⟨U⟩ z
    obtain ⟨n, y, hy⟩ := hcov U z.1 z.2
    refine (congrArg ((Homotopical.MarkedPresheaf.forget.map p).app (op U))
      (glue_app _ _ _ _ _ hcomp z n y hy)).trans ?_
    exact ((φ n).map_app_comp y).trans (congrArg _ hy)

theorem isDegenerate_toFunctor {W : Subfunctor X} {U : Atom} (z : W.toFunctor.obj (op U))
    (hz : IsDegenerate X z.1) : IsDegenerate W.toFunctor z := by
  obtain ⟨V, q, y, hq, hni, hy⟩ := hz
  have := isSplitEpi_of_isCollapseHom q hq
  have hyW : y ∈ W.obj (op V) := by
    have key (y' : X.obj (op V)) : X.map (section_ q).op (X.map q.op y') = y' := by
      rw [← Functor.map_comp_apply, ← op_comp, IsSplitEpi.id, op_id, Functor.map_id_apply]
    have h : X.map (section_ q).op z.1 ∈ W.obj (op V) := W.map _ z.2
    have e : X.map (section_ q).op z.1 = y := by
      rw [← hy]
      exact key y
    exact e ▸ h
  exact ⟨V, q, ⟨y, hyW⟩, hq, hni, Subtype.ext hy⟩

end Chain

theorem PartialLift.exists_coreFiltration_succ {X : DiagSet.{u}} {E F : MarkedDiagSet.{u}}
    {p : E ⟶ F}
    {b : (MarkedDiagSet.markedAboveFunctor 1).obj X ⟶ F}
    (hp : fibrations (MarkedDiagSet.Coinductive 1) ((MarkedDiagSet.toCoinductive 1).map p))
    {m : ℕ} (h2 : 2 ≤ m)
    (con : ∀ B : Atom, IsCore B → B.dimension = m → CoherentContraction B X)
    (φ : PartialLift p b (coreFiltration (m - 1) X)) :
    ∃ φ' : PartialLift p b (coreFiltration m X), ∀ {U : Atom}
      (z : (coreFiltration (m - 1) X).toFunctor.obj (op U)),
      φ'.map.app (op U) ⟨z.1, coreFiltration_mono X (Nat.sub_le m 1) _ z.2⟩ =
        φ.map.app (op U) z := by
  choose next hnext using fun n (ψ : PartialLift p b (attachStage X m con n)) =>
    PartialLift.exists_attachStage_succ hp h2 ψ
  let φ₀ : PartialLift p b (attachStage X m con 0) :=
    PartialLift.ofLE (fun _ _ hz => mem_attachStage_zero.1 hz) φ
  let ψ : ∀ n, PartialLift p b (attachStage X m con n) := fun n =>
    Nat.rec (motive := fun n => PartialLift p b (attachStage X m con n)) φ₀ next n
  obtain ⟨φ', hφ'⟩ := PartialLift.exists_of_chain (fun _ _ h => attachStage_mono h) ψ
    (fun n _ z => hnext n (ψ n) z) (coreFiltration m X) (attachStage_le_coreFiltration)
    (fun _ _ hz => exists_mem_attachStage h2 hz)
  exact ⟨φ', fun z => hφ' 0 ⟨z.1, Or.inl z.2⟩⟩

theorem weakEquivalence_markedAboveFunctor_map_coreFiltration_ι (X : DiagSet.{u})
    (hX : ∀ B : Atom, IsCore B → 2 ≤ B.dimension → Nonempty (CoherentContraction B X)) :
    WeakEquivalence
      ((MarkedDiagSet.Coinductive.markedAboveFunctor 1).map (coreFiltration 1 X).ι) := by
  have key {E F : MarkedDiagSet.{u}} (p : E ⟶ F)
      (hp : fibrations (MarkedDiagSet.Coinductive 1) ((MarkedDiagSet.toCoinductive 1).map p)) :
      HasLiftingProperty ((MarkedDiagSet.markedAboveFunctor 1).map (coreFiltration 1 X).ι) p := by
    refine ⟨fun {t b} sq => ?_⟩
    let φ₁ : PartialLift p b (coreFiltration 1 X) :=
      { map := Homotopical.MarkedPresheaf.forget.map t
        map_mem_marked := fun U z hz => Homotopical.MarkedPresheaf.map_mem_marked t
          ((Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ U z).2
            (hz.imp_left (isDegenerate_toFunctor z)))
        map_comp := by
          have h := congrArg Homotopical.MarkedPresheaf.forget.map sq.w
          rw [Functor.map_comp, Functor.map_comp, MarkedDiagSet.forget_map_markedAboveFunctor_map]
            at h
          exact h }
    choose next hnext using fun m (φ : PartialLift p b (coreFiltration (m + 1) X)) =>
      PartialLift.exists_coreFiltration_succ hp (m := m + 2) (by omega)
        (fun B hB hd => (hX B hB (by omega)).some) φ
    let ψ : ∀ m, PartialLift p b (coreFiltration (m + 1) X) := fun m =>
      Nat.rec (motive := fun m => PartialLift p b (coreFiltration (m + 1) X)) φ₁ next m
    obtain ⟨φ', hφ'⟩ := PartialLift.exists_of_chain (W := fun m => coreFiltration (m + 1) X)
      (fun _ _ h => coreFiltration_mono X (by omega)) ψ (fun m _ z => hnext m (ψ m) z) ⊤
      (fun _ => le_top) (fun U z _ => ⟨U.dimension, coreFiltration_mono X (Nat.le_succ _) _
        ⟨U, 0, 𝟙 U, z, le_rfl, Functor.map_id_apply X (op U) z⟩⟩)
    let l : (MarkedDiagSet.markedAboveFunctor 1).obj X ⟶ E :=
      Homotopical.MarkedPresheaf.homMk (X := MarkedDiagSet.markedAbove X 1)
        (Subfunctor.lift (𝟙 X) le_top ≫ φ'.map) fun V z hz =>
          φ'.map_mem_marked V _ ((Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ V z).1 hz)
    refine CommSq.HasLift.mk' ⟨l, Homotopical.MarkedPresheaf.hom_ext ?_,
      Homotopical.MarkedPresheaf.hom_ext ?_⟩
    · ext ⟨U⟩ z
      exact hφ' 0 z
    · ext ⟨U⟩ z
      exact φ'.map_app_comp _
  exact weakEquivalence_of_hasLiftingProperty _ fun _ _ p _ _ hp => key p hp.mem

end Atoms.Diagrammatic

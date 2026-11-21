import Atoms.Diagrammatic.DiagrammaticSet
import Atoms.Homotopical.HomotopyColimit.ProjectiveCofibration
import Atoms.Shape.Cone
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Atoms.ForMathlib.CategoryTheory.Presentable.Presheaf

open CategoryTheory Limits Simplicial Atoms.Shape Opposite

universe w w' u

namespace Atoms.Diagrammatic

noncomputable def _root_.SSet.toDiagSet : SSet.{u} ⥤ DiagSet.{u} := simplexFunctor.op.lan

def DiagSet.toSSet : DiagSet.{u} ⥤ SSet.{u} :=
  (Functor.whiskeringLeft _ _ _).obj simplexFunctor.op

noncomputable def sSetDiagSetAdj : SSet.toDiagSet.{u} ⊣ DiagSet.toSSet.{u} :=
  simplexFunctor.op.lanAdjunction _

instance preservesLimitsOfSize_toSSet : PreservesLimitsOfSize.{w, w'} DiagSet.toSSet.{u} :=
  sSetDiagSetAdj.rightAdjoint_preservesLimits

noncomputable def toSSetObjBallPointIso : DiagSet.toSSet.obj (ball.{u} atomPoint) ≅ Δ[0] :=
  (isTerminalBallAtomPoint.isTerminalObj DiagSet.toSSet _).uniqueUpToIso
    SSet.stdSimplex.isTerminalObj₀

noncomputable def stdSimplexCompToDiagSetIso :
    SSet.stdSimplex ⋙ SSet.toDiagSet.{u} ≅ simplexFunctor ⋙ uliftYoneda.{u} :=
  (Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{u} simplexFunctor).symm

noncomputable def toDiagSetObjStdSimplexIso (n : ℕ) :
    SSet.toDiagSet.{u}.obj Δ[n] ≅ ball (atomSimplex n) :=
  stdSimplexCompToDiagSetIso.app ⦋n⦌

theorem toDiagSetObjStdSimplexIso_hom_app_map {a b : ℕ} (e : ⦋a⦌ ⟶ ⦋b⦌) (U : Atomᵒᵖ)
    (x : (SSet.toDiagSet.{u}.obj Δ[a]).obj U) :
    (toDiagSetObjStdSimplexIso b).hom.app U
        ((SSet.toDiagSet.map (SSet.stdSimplex.map e)).app U x) =
      ULift.up (((toDiagSetObjStdSimplexIso a).hom.app U x).down ≫ simplexHom e.toOrderHom) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (stdSimplexCompToDiagSetIso.hom.naturality e) U) x
  simp only [Functor.comp_obj, Functor.comp_map, NatTrans.comp_app, ConcreteCategory.comp_apply,
    uliftYoneda_map_app] at h
  exact h

theorem toDiagSetObjStdSimplexIso_hom_app_unit_id (m : ℕ) :
    (toDiagSetObjStdSimplexIso.{u} m).hom.app (op (atomSimplex m))
      ((sSetDiagSetAdj.unit.app Δ[m]).app (op ⦋m⦌)
        (SSet.stdSimplex.objEquiv.symm (𝟙 _))) = ULift.up (𝟙 (atomSimplex m)) :=
  Presheaf.compULiftYonedaIsoULiftYonedaCompLan_inv_app_app_apply_eq_id.{u} simplexFunctor ⦋m⦌

theorem toDiagSetObjStdSimplexIso_hom_app_unit {m n : ℕ} (σ : ⦋m⦌ ⟶ ⦋n⦌) :
    (toDiagSetObjStdSimplexIso.{u} n).hom.app (op (atomSimplex m))
      ((sSetDiagSetAdj.unit.app Δ[n]).app (op ⦋m⦌) (SSet.stdSimplex.objEquiv.symm σ)) =
        ULift.up (simplexHom σ.toOrderHom) := by
  have hσ : SSet.stdSimplex.objEquiv.symm σ = (SSet.stdSimplex.map σ).app (op ⦋m⦌)
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋m⦌)) := by
    rw [← SSet.stdSimplex.objEquiv_symm_comp, Category.id_comp]
  have hu := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sSetDiagSetAdj.unit.naturality (SSet.stdSimplex.map σ)) (op ⦋m⦌))
    (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋m⦌))
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Functor.id_map] at hu
  rw [hσ, hu]
  refine (toDiagSetObjStdSimplexIso_hom_app_map σ _ _).trans ?_
  rw [toDiagSetObjStdSimplexIso_hom_app_unit_id]
  exact congrArg ULift.up (Category.id_comp _)

theorem homEquiv_toDiagSetObjStdSimplexIso_hom_app (n : ℕ) (d : SimplexCategoryᵒᵖ)
    (σ : (Δ[n] : SSet.{u}).obj d) :
    (sSetDiagSetAdj.homEquiv _ _ (toDiagSetObjStdSimplexIso n).hom).app d σ =
      ULift.up (simplexHom (SSet.stdSimplex.objEquiv σ).toOrderHom) := by
  rw [Adjunction.homEquiv_unit]
  exact (congrArg (fun τ => (toDiagSetObjStdSimplexIso n).hom.app (op (atomSimplex _))
    ((sSetDiagSetAdj.unit.app Δ[n]).app d τ))
      (SSet.stdSimplex.objEquiv.symm_apply_apply σ).symm).trans
    (toDiagSetObjStdSimplexIso_hom_app_unit (SSet.stdSimplex.objEquiv σ))

theorem homEquiv_symm_yonedaEquiv_symm {X : DiagSet.{u}} {n : ℕ}
    (e : (DiagSet.toSSet.obj X).obj (op ⦋n⦌)) :
    (sSetDiagSetAdj.homEquiv _ _).symm (SSet.yonedaEquiv.symm e) =
      (toDiagSetObjStdSimplexIso n).hom ≫ uliftYonedaEquiv.symm e := by
  refine ((sSetDiagSetAdj.homEquiv _ _).symm_apply_eq.2 ?_)
  refine Eq.trans ?_ (sSetDiagSetAdj.homEquiv_naturality_right _ _).symm
  ext d σ
  refine Eq.trans ?_ (congrArg
    (fun f : ULift (atomSimplex _ ⟶ atomSimplex n) => X.map f.down.op e)
    (homEquiv_toDiagSetObjStdSimplexIso_hom_app n d σ)).symm
  rfl

theorem injective_toDiagSet_map_app {a b : ℕ} (e : ⦋a⦌ ⟶ ⦋b⦌) [Mono e] (U : Atomᵒᵖ) :
    Function.Injective ((SSet.toDiagSet.{u}.map (SSet.stdSimplex.map e)).app U) := by
  intro x y h
  have h' := congrArg ((toDiagSetObjStdSimplexIso b).hom.app U) h
  rw [toDiagSetObjStdSimplexIso_hom_app_map, toDiagSetObjStdSimplexIso_hom_app_map] at h'
  have := mono_of_isInclusionHom _ (isInclusionHom_simplexHom_of_injective e.toOrderHom
    (SimplexCategory.mono_iff_injective.1 inferInstance))
  have h'' := ULift.ext _ _ ((cancel_mono (simplexHom e.toOrderHom)).1 (congrArg ULift.down h'))
  exact (mono_iff_injective ((toDiagSetObjStdSimplexIso.{u} a).hom.app U)).1 inferInstance h''

theorem mono_toDiagSet_map_boundary_ι (n : ℕ) :
    Mono (SSet.toDiagSet.{u}.map (SSet.boundary n).ι) := by
  have : PreservesColimitsOfSize.{0, 0} SSet.toDiagSet.{u} :=
    sSetDiagSetAdj.leftAdjoint_preservesColimits
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [mono_iff_injective]
  cases n with
  | zero =>
    rw [SSet.boundary_zero]
    have h := ((SSet.Subcomplex.isInitialBot (X := Δ[0])).isInitialObj SSet.toDiagSet).isInitialObj
      ((evaluation Atomᵒᵖ (Type u)).obj U)
    have : IsEmpty ((SSet.toDiagSet.obj ((⊥ : (Δ[0] : SSet.{u}).Subcomplex) : SSet)).obj U) :=
      (Types.initial_iff_empty _).1 ⟨h⟩
    exact fun x => isEmptyElim x
  | succ m =>
    set F : Fin (m + 2) → (Δ[m + 1] : SSet.{u}).Subcomplex := fun i => SSet.stdSimplex.face {i}ᶜ
    have hF : ∀ i, F i ≤ SSet.boundary (m + 1) := fun i => by
      rw [SSet.boundary_eq_iSup]
      exact le_iSup (fun i => SSet.stdSimplex.face ({i}ᶜ : Finset (Fin (m + 2)))) i
    set ψ := (toDiagSetObjStdSimplexIso.{u} (m + 1)).hom.app U
    have hψ : Function.Injective ψ := (mono_iff_injective ψ).1 inferInstance
    have hFι : ∀ i, (F i).ι = (SSet.stdSimplex.faceSingletonComplIso i).inv ≫
        SSet.stdSimplex.δ i := fun i =>
      (Iso.eq_inv_comp _).2 (SSet.stdSimplex.faceSingletonComplIso_hom_ι i).symm
    have hinj : ∀ i, Function.Injective ((SSet.toDiagSet.map (F i).ι).app U) := by
      intro i
      rw [hFι, Functor.map_comp, NatTrans.comp_app]
      intro x y hxy
      simp only [ConcreteCategory.comp_apply] at hxy
      exact (mono_iff_injective _).1 inferInstance
        (injective_toDiagSet_map_app (SimplexCategory.δ i) U hxy)
    have himgF : ∀ i a, atomSimplexVertices (m + 1)
        (ConcreteCategory.hom (ψ ((SSet.toDiagSet.map (F i).ι).app U a)).down
          U.unop.top) ⊆ ({i}ᶜ : Finset _) := by
      intro i a
      rw [hFι, Functor.map_comp, NatTrans.comp_app, ConcreteCategory.comp_apply]
      have h := toDiagSetObjStdSimplexIso_hom_app_map (SimplexCategory.δ i) U
        ((SSet.toDiagSet.map (SSet.stdSimplex.faceSingletonComplIso i).inv).app U a)
      refine ((exists_comp_simplexHom_eq_iff (SimplexCategory.mono_iff_injective.1
        inferInstance) _).1 ⟨_, congrArg ULift.down h.symm⟩).trans ?_
      intro l hl
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hl
      simp only [Finset.mem_compl, Finset.mem_singleton]
      exact Fin.succAbove_ne i k
    have hcomp : ∀ i a, (SSet.toDiagSet.map (SSet.boundary (m + 1)).ι).app U
        ((SSet.toDiagSet.map (SSet.Subcomplex.homOfLE (hF i))).app U a) =
          (SSet.toDiagSet.map (F i).ι).app U a := fun i a => by
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← Functor.map_comp,
        SSet.Subcomplex.homOfLE_ι]
    have hS : ∀ x, ∃ i a, (SSet.toDiagSet.map (SSet.Subcomplex.homOfLE (hF i))).app U a = x := by
      have hd : CompleteLattice.MulticoequalizerDiagram (SSet.boundary (m + 1)) F
          (fun i j => F i ⊓ F j) := ⟨(SSet.boundary_eq_iSup _).symm, fun _ _ => rfl⟩
      have hc := isColimitOfPreserves ((evaluation Atomᵒᵖ (Type u)).obj U)
        (isColimitOfPreserves SSet.toDiagSet (SSet.Subcomplex.MulticoequalizerDiagram.isColimit hd))
      intro x
      obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hc x
      cases j with
      | left p =>
        have hw := ConcreteCategory.congr_hom
          (Cocone.w (((evaluation Atomᵒᵖ (Type u)).obj U).mapCocone
            (SSet.toDiagSet.mapCocone (hd.multicofork.map SSet.Subcomplex.toSSetFunctor)))
            (WalkingMultispan.Hom.fst (J := .prod (Fin (m + 2))) p)) y
        rw [ConcreteCategory.comp_apply] at hw
        exact ⟨p.1, _, hw.trans hy⟩
      | right i => exact ⟨i, y, hy⟩
    have hE : ∀ i j, i < j → ∀ a b, (SSet.toDiagSet.map (F i).ι).app U a =
        (SSet.toDiagSet.map (F j).ι).app U b →
        ∃ w, (SSet.toDiagSet.map (SSet.Subcomplex.homOfLE (inf_le_left (b := F j)))).app U w = a ∧
          (SSet.toDiagSet.map (SSet.Subcomplex.homOfLE (inf_le_right (a := F i)))).app U w = b := by
      intro i j hij a b hab
      have hVi := himgF i a
      have hVj := himgF j b
      rw [← hab] at hVj
      set g : U.unop ⟶ atomSimplex (m + 1) := (ψ ((SSet.toDiagSet.map (F i).ι).app U a)).down
      have hVne : (atomSimplexVertices (m + 1) (g U.unop.top)).Nonempty :=
        Atoms.Molecule.OGP.simplexVertices_nonempty _ _
      cases m with
      | zero =>
        exfalso
        obtain ⟨l, hl⟩ := hVne
        have h₁ := Finset.mem_compl.1 (hVi hl)
        have h₂ := Finset.mem_compl.1 (hVj hl)
        rw [Finset.mem_singleton] at h₁ h₂
        have := Fin.val_ne_of_ne h₁
        have := Fin.val_ne_of_ne h₂
        have : i.1 < j.1 := hij
        omega
      | succ m' =>
        let e : ⦋m'⦌ ⟶ ⦋m' + 1 + 1⦌ :=
          SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt hij)) ≫ SimplexCategory.δ j
        have he : Function.Injective e.toOrderHom :=
          SimplexCategory.mono_iff_injective.1 inferInstance
        have hsub : atomSimplexVertices (m' + 1 + 1) (g U.unop.top) ⊆
            Finset.univ.image e.toOrderHom := by
          intro l hl
          have h₁ := Finset.mem_compl.1 (hVi hl)
          have h₂ := Finset.mem_compl.1 (hVj hl)
          rw [Finset.mem_singleton] at h₁ h₂
          have hl' : l ∈ ({i, j}ᶜ : Finset (Fin (m' + 3))) := by simp [h₁, h₂]
          refine Finset.mem_image.2 ⟨(SSet.stdSimplex.finOrderIsoPairCompl i j hij).symm
            ⟨l, hl'⟩, Finset.mem_univ _, ?_⟩
          have h := SSet.stdSimplex.finOrderIsoPairCompl_apply_val i j hij
            ((SSet.stdSimplex.finOrderIsoPairCompl i j hij).symm ⟨l, hl'⟩)
          rw [OrderIso.apply_symm_apply] at h
          exact h.symm
        obtain ⟨g', hg'⟩ :=
          (exists_comp_simplexHom_eq_iff (m := m') (n := m' + 1 + 1) he g).2 hsub
        have hle : SSet.stdSimplex.face ({i, j}ᶜ : Finset (Fin (m' + 3))) ≤ F i ⊓ F j :=
          le_inf ((SSet.stdSimplex.face_le_face_iff _ _).2 (by simp))
            ((SSet.stdSimplex.face_le_face_iff _ _).2 (by simp))
        let κ := (SSet.stdSimplex.facePairComplIso i j hij).hom ≫ SSet.Subcomplex.homOfLE hle
        have hκ : κ ≫ (F i ⊓ F j).ι = SSet.stdSimplex.map e := by
          rw [Category.assoc, SSet.Subcomplex.homOfLE_ι,
            SSet.stdSimplex.facePairComplIso_hom_ι]
          exact (SSet.stdSimplex.map_comp _ _).symm
        obtain ⟨y, hy⟩ := (epi_iff_surjective ((toDiagSetObjStdSimplexIso m').hom.app U)).1
          inferInstance ⟨g'⟩
        set w := (SSet.toDiagSet.map κ).app U y
        have hw : (SSet.toDiagSet.map (F i ⊓ F j).ι).app U w =
            (SSet.toDiagSet.map (F i).ι).app U a := by
          have h₁ : (SSet.toDiagSet.map (F i ⊓ F j).ι).app U w =
              (SSet.toDiagSet.map (SSet.stdSimplex.map e)).app U y := by
            rw [← hκ, Functor.map_comp, NatTrans.comp_app, ConcreteCategory.comp_apply]
          rw [h₁]
          refine hψ ?_
          simp only [ψ]
          rw [toDiagSetObjStdSimplexIso_hom_app_map, hy]
          exact ULift.ext _ _ hg'
        refine ⟨w, hinj i ?_, hinj j ?_⟩
        · rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← Functor.map_comp,
            SSet.Subcomplex.homOfLE_ι, hw]
        · rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← Functor.map_comp,
            SSet.Subcomplex.homOfLE_ι, hw, hab]
    have hglue : ∀ i j w, (SSet.toDiagSet.map (SSet.Subcomplex.homOfLE (hF i))).app U
        ((SSet.toDiagSet.map (SSet.Subcomplex.homOfLE (inf_le_left (b := F j)))).app U w) =
          (SSet.toDiagSet.map (SSet.Subcomplex.homOfLE (hF j))).app U
            ((SSet.toDiagSet.map (SSet.Subcomplex.homOfLE (inf_le_right (a := F i)))).app U w) :=
      fun i j w => by
        rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← Functor.map_comp,
          SSet.Subcomplex.homOfLE_comp, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
          ← Functor.map_comp, SSet.Subcomplex.homOfLE_comp]
    intro x y hxy
    obtain ⟨i, a, rfl⟩ := hS x
    obtain ⟨j, b, rfl⟩ := hS y
    rw [hcomp, hcomp] at hxy
    rcases lt_trichotomy i j with hij | rfl | hij
    · obtain ⟨w, rfl, rfl⟩ := hE i j hij a b hxy
      exact hglue i j w
    · rw [hinj i hxy]
    · obtain ⟨w, rfl, rfl⟩ := hE j i hij b a hxy.symm
      exact (hglue j i w).symm

instance preservesMonomorphisms_toDiagSet : SSet.toDiagSet.{u}.PreservesMonomorphisms := by
  refine ⟨fun {X Y} i hi => ?_⟩
  have hmono : MorphismProperty.monomorphisms DiagSet.{u} =
      (MorphismProperty.monomorphisms DiagSet.{u}).rlp.llp := by
    rw [monomorphisms_eq_saturation_sphereInclusions.{u}, MorphismProperty.rlp_saturation.{u},
      MorphismProperty.saturation_eq_llp_rlp.{u}]
  have h : MorphismProperty.monomorphisms DiagSet.{u} (SSet.toDiagSet.map i) := by
    rw [hmono]
    intro A B g hg
    rw [sSetDiagSetAdj.hasLiftingProperty_iff]
    have hRg : (MorphismProperty.monomorphisms SSet.{u}).rlp (DiagSet.toSSet.map g) := by
      rw [SSet.rlp_monomorphisms]
      rintro _ _ j ⟨n⟩
      rw [← sSetDiagSetAdj.hasLiftingProperty_iff]
      exact hg _ (mono_toDiagSet_map_boundary_ι n)
    exact hRg i hi
  exact h

theorem exists_toDiagSet_obj_map_lanUnit_eq (P : SSet.{u}) {U : Atom}
    (y : (SSet.toDiagSet.obj P).obj (op U)) :
    ∃ (n : SimplexCategory) (g : U ⟶ simplexFunctor.obj n) (z : P.obj (op n)),
      (SSet.toDiagSet.obj P).map g.op ((simplexFunctor.op.lanUnit.app P).app (op n) z) = y := by
  let e := simplexFunctor.op.leftKanExtensionObjIsoColimit P (op U)
  obtain ⟨f, z, hz⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit _) (e.hom y)
  refine ⟨f.left.unop, f.hom.unop, z, ?_⟩
  have h := ConcreteCategory.congr_hom
    (simplexFunctor.op.ι_leftKanExtensionObjIsoColimit_inv P (op U) f) z
  exact h.symm.trans ((congrArg e.inv hz).trans (e.hom_inv_id_apply y))

theorem toDiagSet_obj_map_comp_lanUnit (P : SSet.{u}) {U : Atom} {m n : SimplexCategory}
    (g : U ⟶ simplexFunctor.obj m) (θ : m ⟶ n) (z : P.obj (op n)) :
    (SSet.toDiagSet.obj P).map (g ≫ simplexFunctor.map θ).op
        ((simplexFunctor.op.lanUnit.app P).app (op n) z) =
      (SSet.toDiagSet.obj P).map g.op
        ((simplexFunctor.op.lanUnit.app P).app (op m) (P.map θ.op z)) := by
  have h := NatTrans.naturality_apply (simplexFunctor.op.lanUnit.app P) θ.op z
  rw [op_comp]
  exact (Functor.map_comp_apply (SSet.toDiagSet.obj P) _ _ _).trans (congrArg _ h.symm)

theorem sSetDiagSetAdj_counit_app_app_map_lanUnit (X : DiagSet.{u}) {U : Atom}
    {n : SimplexCategory} (g : U ⟶ simplexFunctor.obj n)
    (z : X.obj (op (simplexFunctor.obj n))) :
    (sSetDiagSetAdj.counit.app X).app (op U)
      ((SSet.toDiagSet.obj (DiagSet.toSSet.obj X)).map g.op
        ((simplexFunctor.op.lanUnit.app (DiagSet.toSSet.obj X)).app (op n) z)) =
      X.map g.op z := by
  have h := ConcreteCategory.congr_hom
    (simplexFunctor.op.lanUnit_app_app_lanAdjunction_counit_app_app X (op n)) z
  refine (NatTrans.naturality_apply (sSetDiagSetAdj.counit.app X) g.op _).trans ?_
  exact congrArg (X.map g.op) h

end Atoms.Diagrammatic

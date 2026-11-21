import Atoms.Molecule.Labelling.Commutative
import Atoms.ForMathlib.CategoryTheory.Bicategory.Functor.PathComp

open CategoryTheory CategoryTheory.Bicategory Order

universe w v u₁ w₂ v₂ u₂ w₃ v₃ u₃ u u'

namespace Atoms.Molecule.OGP

variable {B : Type u₁} [Bicategory.{w, v} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {P : OGP.{u}} [Fintype P] [DecidableLE P] {hP : P.IsRDC}

namespace Labelling

def map (F : B ⥤ᵖ C) (ℓ : Labelling B P hP) : Labelling C P hP where
  toPrefunctor := ℓ.toPrefunctor ⋙q F.toPrefunctor
  obj_eq_of_boundary_Iic x _ hv := congrArg F.obj (ℓ.obj_eq_of_boundary_Iic x hv)
  cell x hx _ _ hs ht := pathCompMap₂ ℓ.toPrefunctor F (ℓ.cell x hx hs ht)

theorem map_toPrefunctor (F : B ⥤ᵖ C) (ℓ : Labelling B P hP) :
    (ℓ.map F).toPrefunctor = ℓ.toPrefunctor ⋙q F.toPrefunctor :=
  rfl

theorem map_id (ℓ : Labelling B P hP) : ℓ.map (Pseudofunctor.id B) = ℓ :=
  Labelling.ext rfl fun x hx _ _ hs ht =>
    heq_of_eq (pathCompMap₂_idPseudofunctor ℓ.toPrefunctor (ℓ.cell x hx hs ht))

theorem map_comp {D : Type u₃} [Bicategory.{w₃, v₃} D] (F : B ⥤ᵖ C) (G : C ⥤ᵖ D)
    (ℓ : Labelling B P hP) : ℓ.map (F.comp G) = (ℓ.map F).map G :=
  Labelling.ext rfl fun x hx _ _ hs ht =>
    heq_of_eq (pathCompMap₂_compPseudofunctor ℓ.toPrefunctor F G (ℓ.cell x hx hs ht))

variable (F : B ⥤ᵖ C) (ℓ : Labelling B P hP) {M : LowerSet P} [DecidablePred (· ∈ M)]
  (hM : IsMoleculeIn P M) {xs : List P} (h : IsLayerOrder M xs) {s t : P}
  (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t)

theorem layerComp_map {j : ℕ} (hj : j < xs.length) :
    (ℓ.map F).layerComp hM h hs ht j hj =
      pathCompMap₂ ℓ.toPrefunctor F (ℓ.layerComp hM h hs ht j hj) := by
  have ha := boundary_zero_eq_Iic_vertex _ (hP xs[j]) false
  have hb := boundary_zero_eq_Iic_vertex _ (hP xs[j]) true
  obtain ⟨p, c, e⟩ := h.exists_stagePath_eq hs ht hM hj ha hb
  have e' := h.comp_comp_eq_stagePath hs ht hM hj rfl (hP xs[j]) ha hb p c e
  exact ((ℓ.map F).layerComp_eq hM h hs ht hj rfl ha hb p c e e').trans
    (((congrArg (fun t => eqToHom _ ≫ t ≫ eqToHom _)
      (pathCompMap₂_pathWhisker _ F p _ c)).symm.trans
      (pathCompMap₂_eqToHom_comp_eqToHom _ F e e' _).symm).trans
        (congrArg (pathCompMap₂ ℓ.toPrefunctor F)
          (ℓ.layerComp_eq hM h hs ht hj rfl ha hb p c e e').symm))

theorem compositeUpTo_map : ∀ (n : ℕ) (hn : n ≤ xs.length),
    (ℓ.map F).compositeUpTo hM h hs ht n hn =
      pathCompMap₂ ℓ.toPrefunctor F (ℓ.compositeUpTo hM h hs ht n hn)
  | 0, _ => (pathCompMap₂_id ℓ.toPrefunctor F _).symm
  | n + 1, hn => (congrArg₂ (· ≫ ·) (compositeUpTo_map n (by omega))
      (layerComp_map F ℓ hM h hs ht hn)).trans (pathCompMap₂_comp ℓ.toPrefunctor F _ _).symm

theorem compositeAlong_map :
    (ℓ.map F).compositeAlong hM h hs ht =
      pathCompMap₂ ℓ.toPrefunctor F (ℓ.compositeAlong hM h hs ht) :=
  (congrArg (fun t => eqToHom _ ≫ t ≫ eqToHom _)
    (compositeUpTo_map F ℓ hM h hs ht xs.length le_rfl)).trans
    (pathCompMap₂_eqToHom_comp_eqToHom ℓ.toPrefunctor F (stagePath_zero hM h hs ht).symm
      (stagePath_length hM h hs ht) _).symm

theorem pathCell_map :
    (ℓ.map F).pathCell hM h hs ht = (ℓ.pathCell hM h hs ht).map F :=
  (congrArg (PathCell.ofHom (ℓ.toPrefunctor ⋙q F.toPrefunctor) _ _)
    (compositeAlong_map F ℓ hM h hs ht)).trans
    (PathCell.map_ofHom ℓ.toPrefunctor F _ _ (ℓ.compositeAlong hM h hs ht)).symm

theorem IsCommutative.map {ℓ : Labelling B P hP} (hℓ : ℓ.IsCommutative) :
    (ℓ.map F).IsCommutative := fun y hy =>
  isCommutativeAt_of_pathCell_eq fun hs ht _ _ hxs hys =>
    (pathCell_map F ℓ _ hxs _ _).trans ((congrArg (PathCell.map · F)
      (IsCommutativeAt.pathCell_eq (hℓ y hy) hs ht hxs hys)).trans
        (pathCell_map F ℓ _ hys _ _).symm)

end Labelling

variable {Q : OGP.{u'}} [Fintype Q] [DecidableLE Q] {hQ : Q.IsRDC}

private theorem eqToHom_comp_comp_comp_comp_eqToHom {D : Type*} [Category D]
    {x x' x'' y y' y'' a b : D} (M₁ : x'' ⟶ a) (M₂ : a ⟶ b) (M₃ : b ⟶ y'') (hx : x = x')
    (hx' : x' = x'') (hy : y'' = y') (hy' : y' = y) :
    eqToHom (hx.trans hx') ≫ M₁ ≫ M₂ ≫ M₃ ≫ eqToHom (hy.trans hy') =
      eqToHom hx ≫ (eqToHom hx' ≫ M₁ ≫ M₂ ≫ M₃ ≫ eqToHom hy) ≫ eqToHom hy' := by
  subst hx hx' hy hy'
  simp

omit [Fintype P] [DecidableLE P] [Fintype Q] [DecidableLE Q] in
theorem Map.isGeneratorOrId_freePrefunctor_map (f : Map P Q) {v w : EdgeQuiver P} (e : v ⟶ w) :
    FreeBicategory.Hom.IsGeneratorOrId (f.freePrefunctor.map e) := by
  by_cases he : grade ℕ (f e.1) = 1
  · rw [f.freePrefunctor_map_of_grade_eq e he]
    exact .of _
  · rw [f.freePrefunctor_map_of_grade_ne e he]
    exact FreeBicategory.Hom.isGeneratorOrId_homOfEq_id _

theorem Labelling.map_comap (f : Map P Q) (F : StrictlyUnitaryPseudofunctor B C)
    (ℓ : Labelling B Q hQ) :
    (ℓ.comap f hP).map F.toPseudofunctor = (ℓ.map F.toPseudofunctor).comap f hP := by
  have hf {v w : EdgeQuiver P} (e : v ⟶ w) :
      FreeBicategory.Hom.IsGeneratorOrId (f.freePrefunctor.map e) :=
    f.isGeneratorOrId_freePrefunctor_map e
  have hl {s t : P} (q : Quiver.Path (V := EdgeQuiver P) s t) :=
    pathComp_comp_lift f.freePrefunctor (ℓ.map F.toPseudofunctor).toPrefunctor q
  have hp {s t : P} (q : Quiver.Path (V := EdgeQuiver P) s t) :
      pathComp ((ℓ.comap f hP).map F.toPseudofunctor).toPrefunctor q =
        pathComp ((ℓ.map F.toPseudofunctor).comap f hP).toPrefunctor q :=
    (pathComp_comp_lift_comp ℓ.toPrefunctor F f.freePrefunctor hf q).trans (hl q).symm
  refine Labelling.ext (Prefunctor.ext (fun _ => rfl) fun _ _ e =>
    map_lift_map_of_isGeneratorOrId ℓ.toPrefunctor F (hf e))
    fun x hx s t hs ht => (conj_eqToHom_iff_heq _ _ (hp _) (hp _)).1 ?_
  by_cases h2 : grade ℕ (f x) = 2
  · rw [comap_cell_of_grade_eq f (ℓ.map F.toPseudofunctor) hx h2 hs ht]
    exact ((congrArg (pathCompMap₂ _ F.toPseudofunctor)
      (comap_cell_of_grade_eq f ℓ hx h2 hs ht)).trans
        (pathCompMap₂_comp_lift_map₂_comp_comp ℓ.toPrefunctor F f.freePrefunctor hf _ _ _)).trans
          (eqToHom_comp_comp_comp_comp_eqToHom _ _ _ (hp _) (hl _) (hl _).symm (hp _).symm)
  · obtain ⟨θ, h⟩ := comap_cell_of_grade_ne f ℓ hx h2 hs ht
    obtain ⟨θ', h'⟩ := comap_cell_of_grade_ne f (ℓ.map F.toPseudofunctor) hx h2 hs ht
    rw [h', FreeBicategory.lift_map₂_eq _ θ' θ]
    exact ((congrArg (pathCompMap₂ _ F.toPseudofunctor) h).trans
      (pathCompMap₂_comp_lift_map₂ ℓ.toPrefunctor F f.freePrefunctor hf θ)).trans
        (eqToHom_comp_comp_eqToHom_eq _ (hp _) (hl _) (hl _).symm (hp _).symm _ _).symm

end Atoms.Molecule.OGP

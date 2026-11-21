import Atoms.Molecule.Labelling.Pasting
import Atoms.Molecule.RegularComplex.CartesianAtom
import Atoms.ForMathlib.CategoryTheory.Bicategory.Structural
import Atoms.Molecule.ClosedEmbedding
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

universe w v u u' u'' u₁ u₂ v₂

open Order CategoryTheory Bicategory FreeBicategory

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {Q : OGP.{u'}}

namespace Map

variable (f : Map P Q)

def freePrefunctor : Prefunctor (EdgeQuiver P) (FreeBicategory (EdgeQuiver Q)) where
  obj v := f v
  map {v _} e :=
    if he : grade ℕ (f e.1) = 1 then Hom.of (f.mapEdge e he)
    else Quiver.homOfEq (V := FreeBicategory (EdgeQuiver Q)) (Hom.id (B := EdgeQuiver Q) (f v)) rfl
      (f.apply_eq_of_grade_ne e he)

theorem freePrefunctor_map_of_grade_eq {v w : EdgeQuiver P} (e : v ⟶ w)
    (he : grade ℕ (f e.1) = 1) : f.freePrefunctor.map e = Hom.of (f.mapEdge e he) :=
  dif_pos he

theorem freePrefunctor_map_of_grade_ne {v w : EdgeQuiver P} (e : v ⟶ w)
    (he : grade ℕ (f e.1) ≠ 1) :
    f.freePrefunctor.map e = Quiver.homOfEq (V := FreeBicategory (EdgeQuiver Q))
      (Hom.id (B := EdgeQuiver Q) (f v)) rfl (f.apply_eq_of_grade_ne e he) :=
  dif_neg he

theorem normalizeAux_nil_pathComp_freePrefunctor {a : EdgeQuiver P} :
    ∀ {b : EdgeQuiver P} (p : Quiver.Path a b),
      normalizeAux .nil (pathComp f.freePrefunctor p) = f.mapPath p
  | _, .nil => rfl
  | _, .cons p e => by
    rw [pathComp_cons]
    change normalizeAux (normalizeAux .nil (pathComp f.freePrefunctor p)) (f.freePrefunctor.map e) =
      _
    rw [normalizeAux_nil_pathComp_freePrefunctor p, mapPath]
    by_cases he : grade ℕ (f e.1) = 1
    · rw [dif_pos he]
      simp only [freePrefunctor, dif_pos he]
      rfl
    · rw [dif_neg he]
      simp only [freePrefunctor, dif_neg he]
      exact normalizeAux_homOfEq_id _ _

theorem pathComp_freePrefunctor_of_forall {a : EdgeQuiver P} :
    ∀ {b : EdgeQuiver P} (p : Quiver.Path a b), (∀ e ∈ pathEdges p, grade ℕ (f e) = 1) →
      pathComp f.freePrefunctor p = pathComp FreeBicategory.of (f.mapPath p)
  | _, .nil, _ => rfl
  | _, .cons p e, h => by
    have he : grade ℕ (f e.1) = 1 := h e.1 (by simp)
    rw [pathComp_cons, pathComp_freePrefunctor_of_forall p fun d hd => h d (by simp [hd]),
      f.freePrefunctor_map_of_grade_eq e he, mapPath, dif_pos he, pathComp_cons]
    rfl

private theorem lift_map_homOfEq_id {W W' : Type*} [Quiver W] [Quiver W']
    (G : Prefunctor W (FreeBicategory W')) {b c : FreeBicategory W} (h : b = c) :
    (lift G).map (Quiver.homOfEq (𝟙 b) rfl h) =
      Quiver.homOfEq (𝟙 ((lift G).obj b)) rfl (congrArg (lift G).obj h) := by
  subst h
  rfl

theorem lift_map_freePrefunctor_map {R : OGP.{u''}} (g : Map Q R) {v w : EdgeQuiver P}
    (e : v ⟶ w) :
    (lift g.freePrefunctor).map (f.freePrefunctor.map e) = (g.comp f).freePrefunctor.map e := by
  by_cases he : grade ℕ (f e.1) = 1
  · rw [f.freePrefunctor_map_of_grade_eq e he]
    by_cases hg : grade ℕ (g (f e.1)) = 1
    · exact (g.freePrefunctor_map_of_grade_eq _ hg).trans
        ((g.comp f).freePrefunctor_map_of_grade_eq e hg).symm
    · exact (g.freePrefunctor_map_of_grade_ne _ hg).trans
        ((g.comp f).freePrefunctor_map_of_grade_ne e hg).symm
  · have hg : grade ℕ ((g.comp f) e.1) ≠ 1 := by
      have h1 := g.isMap_coe.grade_le (f e.1)
      have h2 := f.isMap_coe.grade_le e.1
      rw [e.2.1] at h2
      rw [Map.comp_apply]
      omega
    rw [f.freePrefunctor_map_of_grade_ne e he, (g.comp f).freePrefunctor_map_of_grade_ne e hg]
    exact lift_map_homOfEq_id _ _

theorem lift_map_pathComp_freePrefunctor {R : OGP.{u''}} (g : Map Q R) {a : EdgeQuiver P} :
    ∀ {b : EdgeQuiver P} (p : Quiver.Path a b),
      (lift g.freePrefunctor).map (pathComp f.freePrefunctor p) =
        pathComp (g.comp f).freePrefunctor p
  | _, .nil => rfl
  | _, .cons p e =>
    congrArg₂ (· ≫ ·) (lift_map_pathComp_freePrefunctor g p) (f.lift_map_freePrefunctor_map g e)

end Map

end Atoms.Molecule.OGP

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {Q : OGP.{u'}} [Fintype P] [DecidableLE P] [Fintype Q] [DecidableLE Q]
  {B : Type u₁} [Bicategory.{w, v} B] {hP : P.IsRDC} {hQ : Q.IsRDC}

abbrev boundaryPath (R : OGP.{u''}) [Fintype R] [DecidableLE R] (hR : R.IsRDC) (x : R)
    (α : Bool) {s t : R} (hs : R.boundary (.Iic x) 0 false = .Iic s)
    (ht : R.boundary (.Iic x) 0 true = .Iic t) : Quiver.Path (V := EdgeQuiver R) s t :=
  pathOf (R.boundary (.Iic x) 1 α) ((hR x).boundary 1 α)
    ((krullDim_boundary_le _ 1 α).trans_eq Nat.cast_one)
    (((hR x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
    (((hR x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)

omit [Fintype P] [DecidableLE P] [Fintype Q] [DecidableLE Q] in
theorem Map.pathComp_freePrefunctor_comp_lift_of_forall (f : Map P Q)
    (G : Prefunctor (EdgeQuiver Q) B) {a b : EdgeQuiver P} (p : Quiver.Path a b)
    (h : ∀ e ∈ pathEdges p, grade ℕ (f e) = 1) :
    pathComp (f.freePrefunctor ⋙q (lift G).toPrefunctor) p = pathComp G (f.mapPath p) :=
  (pathComp_comp_lift _ _ _).trans ((congrArg _ (f.pathComp_freePrefunctor_of_forall _ h)).trans
    (pathComp_comp_lift FreeBicategory.of G _).symm)

omit [Fintype P] [DecidableLE P] [Fintype Q] [DecidableLE Q] in
theorem Map.mapPath_freePrefunctor_comp_lift_of_forall (f : Map P Q)
    (G : Prefunctor (EdgeQuiver Q) B) {a : EdgeQuiver P} :
    ∀ {b : EdgeQuiver P} (p : Quiver.Path a b), (∀ e ∈ pathEdges p, grade ℕ (f e) = 1) →
      (f.freePrefunctor ⋙q (lift G).toPrefunctor).mapPath p = G.mapPath (f.mapPath p)
  | _, .nil, _ => rfl
  | _, .cons p e, h => by
    have he : grade ℕ (f e.1) = 1 := h e.1 (by simp)
    rw [Prefunctor.mapPath_cons, Map.mapPath_freePrefunctor_comp_lift_of_forall f G p
      fun d hd => h d (by simp [hd]), Map.mapPath, dif_pos he, Prefunctor.mapPath_cons]
    exact congrArg _ (congrArg (lift G).map (f.freePrefunctor_map_of_grade_eq e he))

private theorem normalizeAux_boundaryPath (f : Map P Q) (hP : P.IsRDC) (hQ : Q.IsRDC) {x : P}
    (α : Bool) {s t : P} (hs : P.boundary (.Iic x) 0 false = .Iic s)
    (ht : P.boundary (.Iic x) 0 true = .Iic t) :
    normalizeAux .nil (pathComp f.freePrefunctor (boundaryPath P hP x α hs ht)) =
      normalizeAux .nil (inclusionPathAux
        (boundaryPath Q hQ (f x) α (f.boundary_Iic_apply hs) (f.boundary_Iic_apply ht))) :=
  ((f.normalizeAux_nil_pathComp_freePrefunctor _).trans
    (f.mapPath_pathOf_boundary hP hQ x α _ _)).trans (normalizeAux_nil_inclusionPathAux _).symm

private theorem boundaryPath_false_eq_true (R : OGP.{u''}) [Fintype R] [DecidableLE R]
    (hR : R.IsRDC) {z : R} (hz : grade ℕ z ≤ 1) {s t : R}
    (hs : R.boundary (.Iic z) 0 false = .Iic s) (ht : R.boundary (.Iic z) 0 true = .Iic t) :
    boundaryPath R hR z false hs ht = boundaryPath R hR z true hs ht := by
  have hd : krullDim (LowerSet.Iic z) ≤ (1 : ℕ) := by
    rw [LowerSet.krullDim_Iic]
    exact_mod_cast hz
  exact pathOf_congr ((boundary_eq_self hd false).trans (boundary_eq_self hd true).symm)

private theorem conj_eqToHom_eq {C : Type*} [Category C] {U V₁ W₁ V₂ W₂ U' : C} {φ₁ : V₁ ⟶ W₁}
    {φ₂ : V₂ ⟶ W₂} {e₁ : V₁ = W₁} {e₂ : V₂ = W₂} (h₁ : φ₁ = eqToHom e₁) (h₂ : φ₂ = eqToHom e₂)
    (c : W₁ ⟶ V₂) (hU : U = V₁) (hU' : W₂ = U') :
    eqToHom hU ≫ φ₁ ≫ c ≫ φ₂ ≫ eqToHom hU' =
      eqToHom (hU.trans e₁) ≫ c ≫ eqToHom (e₂.trans hU') := by
  subst h₁ h₂ hU hU' e₁ e₂
  simp

private theorem sandwich_eq {W : Type u''} [Quiver W] {F : Prefunctor W B}
    {a b : FreeBicategory W} {X₁ Y₁ X₂ Y₂ : a ⟶ b} {U U' : F.obj a ⟶ F.obj b} (θ₁ : X₁ ⟶ Y₁)
    (C : (lift F).map Y₁ ⟶ (lift F).map X₂) (θ₂ : X₂ ⟶ Y₂) (h₁ : X₁ = Y₁) (h₂ : X₂ = Y₂)
    (hU : U = (lift F).map X₁) (hU' : (lift F).map Y₂ = U') :
    eqToHom hU ≫ (lift F).map₂ θ₁ ≫ C ≫ (lift F).map₂ θ₂ ≫ eqToHom hU' =
      eqToHom (hU.trans (congrArg _ h₁)) ≫ C ≫ eqToHom ((congrArg _ h₂).trans hU') :=
  conj_eqToHom_eq (lift_map₂_eq_eqToHom F θ₁ h₁) (lift_map₂_eq_eqToHom F θ₂ h₂) C hU hU'

namespace Labelling

@[ext]
theorem ext {ℓ ℓ' : Labelling B P hP} (h : ℓ.toPrefunctor = ℓ'.toPrefunctor)
    (hc : ∀ (x : P) (hx : grade ℕ x = 2) {s t : P} (hs : P.boundary (.Iic x) 0 false = .Iic s)
      (ht : P.boundary (.Iic x) 0 true = .Iic t), HEq (ℓ.cell x hx hs ht) (ℓ'.cell x hx hs ht)) :
    ℓ = ℓ' := by
  obtain ⟨F, hF, c⟩ := ℓ
  obtain ⟨F', hF', c'⟩ := ℓ'
  obtain rfl : F = F' := h
  congr
  funext x hx s t hs ht
  exact eq_of_heq (hc x hx hs ht)

theorem obj_eq_obj_vertex (ℓ : Labelling B P hP) (x : P) :
    ℓ.toPrefunctor.obj x = ℓ.toPrefunctor.obj (vertex (.Iic x) (hP x) false) :=
  ℓ.obj_eq_of_boundary_Iic x (boundary_zero_eq_Iic_vertex _ (hP x) false)

theorem ext_of_grade_eq_zero {ℓ ℓ' : Labelling B P hP}
    (hobj : ∀ v : P, grade ℕ v = 0 → ℓ.toPrefunctor.obj v = ℓ'.toPrefunctor.obj v)
    (hmap : ∀ {v w : EdgeQuiver P} (e : v ⟶ w), ℓ.toPrefunctor.map e ≍ ℓ'.toPrefunctor.map e)
    (hc : ∀ (x : P) (hx : grade ℕ x = 2) {s t : P} (hs : P.boundary (.Iic x) 0 false = .Iic s)
      (ht : P.boundary (.Iic x) 0 true = .Iic t), HEq (ℓ.cell x hx hs ht) (ℓ'.cell x hx hs ht)) :
    ℓ = ℓ' :=
  ext (Prefunctor.hext (fun x => (ℓ.obj_eq_obj_vertex x).trans ((hobj _
    (grade_eq_zero_of_boundary_zero_eq_Iic (boundary_zero_eq_Iic_vertex _ (hP x) false))).trans
      (ℓ'.obj_eq_obj_vertex x).symm)) fun _ _ e => hmap e) hc

def free (h : ∀ x : P, grade ℕ x ≠ 2) : Labelling (FreeBicategory (EdgeQuiver P)) P hP where
  toPrefunctor :=
    { obj (x : P) := vertex (.Iic x) (hP x) false
      map e := Quiver.homOfEq (FreeBicategory.of.map e)
        (vertex_Iic_of_boundary_Iic e.2.2.1 _).symm (vertex_Iic_of_boundary_Iic e.2.2.2 _).symm }
  obj_eq_of_boundary_Iic x _ hv := (vertex_eq_of_boundary_zero_eq_Iic _ (hP x) hv).trans
    (vertex_Iic_of_boundary_Iic hv (hP _)).symm
  cell x hx := absurd hx (h x)

theorem free_map_heq (h : ∀ x : P, grade ℕ x ≠ 2) {v w : EdgeQuiver P} (e : v ⟶ w) :
    (free (hP := hP) h).toPrefunctor.map e ≍ (Hom.of e : FreeBicategory.Hom v w) :=
  Quiver.homOfEq_heq _ _ _

theorem free_comp_lift (h : ∀ x : P, grade ℕ x ≠ 2) (G : Prefunctor (EdgeQuiver P) B)
    (hG : ∀ (x : P) {v : P}, P.boundary (.Iic x) 0 false = .Iic v → G.obj x = G.obj v) :
    (free (hP := hP) h).toPrefunctor ⋙q (lift G).toPrefunctor = G := by
  refine Prefunctor.hext
    (fun (x : P) => (hG x (boundary_zero_eq_Iic_vertex _ (hP x) false)).symm) fun _ _ _ => ?_
  exact (heq_of_eq (Prefunctor.homOfEq_map (lift G).toPrefunctor _ _ _)).trans
    (Quiver.homOfEq_heq _ _ _)

def comap (f : Map P Q) (hP : P.IsRDC) (ℓ : Labelling B Q hQ) : Labelling B P hP where
  toPrefunctor := f.freePrefunctor ⋙q (lift ℓ.toPrefunctor).toPrefunctor
  obj_eq_of_boundary_Iic x _ hv := ℓ.obj_eq_of_boundary_Iic (f x) (f.boundary_Iic_apply hv)
  cell x hx s t hs ht :=
    if h2 : grade ℕ (f x) = 2 then
      eqToHom (pathComp_comp_lift _ _ _) ≫
        (lift ℓ.toPrefunctor).map₂
          (homOfNormalizeAuxEq (normalizeAux_boundaryPath f hP hQ false hs ht)) ≫
          ℓ.cell (f x) h2 (f.boundary_Iic_apply hs) (f.boundary_Iic_apply ht) ≫
            (lift ℓ.toPrefunctor).map₂
              (homOfNormalizeAuxEq (normalizeAux_boundaryPath f hP hQ true hs ht).symm) ≫
              eqToHom (pathComp_comp_lift _ _ _).symm
    else
      eqToHom (pathComp_comp_lift _ _ _) ≫
        (lift ℓ.toPrefunctor).map₂ (homOfNormalizeAuxEq
          ((normalizeAux_boundaryPath f hP hQ false hs ht).trans ((congrArg _ (congrArg _
            (boundaryPath_false_eq_true Q hQ (by have := f.isMap_coe.grade_le x; omega) _ _))).trans
              (normalizeAux_boundaryPath f hP hQ true hs ht).symm))) ≫
        eqToHom (pathComp_comp_lift _ _ _).symm

@[simp]
theorem comap_obj (f : Map P Q) (ℓ : Labelling B Q hQ) (v : EdgeQuiver P) :
    (ℓ.comap f hP).toPrefunctor.obj v = ℓ.toPrefunctor.obj (f v) :=
  rfl

theorem comap_cell_of_grade_eq (f : Map P Q) (ℓ : Labelling B Q hQ) {x : P} (hx : grade ℕ x = 2)
    (h2 : grade ℕ (f x) = 2) {s t : P} (hs : P.boundary (.Iic x) 0 false = .Iic s)
    (ht : P.boundary (.Iic x) 0 true = .Iic t) :
    (ℓ.comap f hP).cell x hx hs ht =
      eqToHom (pathComp_comp_lift _ _ _) ≫
        (lift ℓ.toPrefunctor).map₂
          (homOfNormalizeAuxEq (normalizeAux_boundaryPath f hP hQ false hs ht)) ≫
          ℓ.cell (f x) h2 (f.boundary_Iic_apply hs) (f.boundary_Iic_apply ht) ≫
            (lift ℓ.toPrefunctor).map₂
              (homOfNormalizeAuxEq (normalizeAux_boundaryPath f hP hQ true hs ht).symm) ≫
              eqToHom (pathComp_comp_lift _ _ _).symm :=
  dif_pos h2

theorem comap_cell_of_grade_ne (f : Map P Q) (ℓ : Labelling B Q hQ) {x : P} (hx : grade ℕ x = 2)
    (h2 : grade ℕ (f x) ≠ 2) {s t : P} (hs : P.boundary (.Iic x) 0 false = .Iic s)
    (ht : P.boundary (.Iic x) 0 true = .Iic t) :
    ∃ θ, (ℓ.comap f hP).cell x hx hs ht =
      eqToHom (pathComp_comp_lift _ _ _) ≫ (lift ℓ.toPrefunctor).map₂ θ ≫
        eqToHom (pathComp_comp_lift _ _ _).symm :=
  ⟨_, dif_neg h2⟩

theorem cell_heq_of_eq (ℓ : Labelling B P hP) {x x' : P} (e : x = x') (hx : grade ℕ x = 2)
    (hx' : grade ℕ x' = 2) {s t s' t' : P} (hs : P.boundary (.Iic x) 0 false = .Iic s)
    (ht : P.boundary (.Iic x) 0 true = .Iic t) (hs' : P.boundary (.Iic x') 0 false = .Iic s')
    (ht' : P.boundary (.Iic x') 0 true = .Iic t') :
    HEq (ℓ.cell x hx hs ht) (ℓ.cell x' hx' hs' ht') := by
  subst e
  obtain rfl : s = s' := LowerSet.Iic_injective (hs.symm.trans hs')
  obtain rfl : t = t' := LowerSet.Iic_injective (ht.symm.trans ht')
  rfl

theorem conjEqToHom_comap_cell (f : Map P Q) (ℓ : Labelling B Q hQ) {x : P} (hx : grade ℕ x = 2)
    (hgr : ∀ d ≤ x, grade ℕ (f d) = grade ℕ d) {s t : P}
    (hs : P.boundary (.Iic x) 0 false = .Iic s) (ht : P.boundary (.Iic x) 0 true = .Iic t) :
    ConjEqToHom ((ℓ.comap f hP).cell x hx hs ht)
      (ℓ.cell (f x) ((hgr x le_rfl).trans hx) (f.boundary_Iic_apply hs)
        (f.boundary_Iic_apply ht)) := by
  have hcol (α : Bool) : ∀ d ∈ pathEdges (boundaryPath P hP x α hs ht), grade ℕ (f d) = 1 := by
    intro d hd
    rw [pathEdges_pathOf] at hd
    obtain ⟨hdS, hd1⟩ := (mem_edgeList_iff ((hP x).boundary 1 α)
      ((krullDim_boundary_le _ 1 α).trans_eq Nat.cast_one)).1 hd
    rw [hgr d (boundary_le _ _ _ hdS), hd1]
  have he (α : Bool) : pathComp f.freePrefunctor (boundaryPath P hP x α hs ht) =
      inclusionPathAux (boundaryPath Q hQ (f x) α (f.boundary_Iic_apply hs)
        (f.boundary_Iic_apply ht)) :=
    (f.pathComp_freePrefunctor_of_forall _ (hcol α)).trans ((pathComp_of _).trans
      (congrArg _ (f.mapPath_pathOf_boundary hP hQ x α _ _)))
  rw [comap_cell_of_grade_eq f ℓ hx ((hgr x le_rfl).trans hx) hs ht]
  exact ⟨_, _, sandwich_eq (F := ℓ.toPrefunctor) _ _ _ (he false) (he true).symm _ _⟩

theorem conjEqToHom_compositeAlong (ℓ : Labelling B P hP) {M M' : LowerSet P}
    [d : DecidablePred (· ∈ M)] [d' : DecidablePred (· ∈ M')] (e : M = M')
    (hM : IsMoleculeIn P M) (hM' : IsMoleculeIn P M') {xs ys : List P} (hxs : IsLayerOrder M xs)
    (hys : IsLayerOrder M' ys) {s t : P} (hs : P.boundary M 0 false = .Iic s)
    (ht : P.boundary M 0 true = .Iic t) (hs' : P.boundary M' 0 false = .Iic s)
    (ht' : P.boundary M' 0 true = .Iic t) :
    ConjEqToHom (ℓ.compositeAlong hM hxs hs ht) (ℓ.compositeAlong hM' hys hs' ht') := by
  subst e
  obtain rfl : d = d' := Subsingleton.elim _ _
  rw [ℓ.compositeAlong_eq hM hs ht hxs hys]
  exact conjEqToHom_refl _

omit [Fintype P] [DecidableLE P] in
private theorem pathComp_freePrefunctor_id {a : EdgeQuiver P} :
    ∀ {b : EdgeQuiver P} (p : Quiver.Path a b),
      pathComp (Map.id P).freePrefunctor p = inclusionPathAux p
  | _, .nil => rfl
  | _, .cons p e => by
    rw [pathComp_cons, pathComp_freePrefunctor_id p]
    exact congrArg (inclusionPathAux p ≫ ·) ((Map.id P).freePrefunctor_map_of_grade_eq e e.2.1)

theorem comap_id (ℓ : Labelling B P hP) : ℓ.comap (Map.id P) hP = ℓ := by
  have hF : (ℓ.comap (Map.id P) hP).toPrefunctor = ℓ.toPrefunctor := by
    refine Prefunctor.ext (fun _ => rfl) fun v w e => ?_
    exact congrArg (lift ℓ.toPrefunctor).map ((Map.id P).freePrefunctor_map_of_grade_eq e e.2.1)
  refine ext hF fun x hx s t hs ht => ?_
  have hp (q : Quiver.Path (V := EdgeQuiver P) s t) :
      pathComp (ℓ.comap (Map.id P) hP).toPrefunctor q = pathComp ℓ.toPrefunctor q :=
    (pathComp_comp_lift _ _ q).trans (congrArg _ (pathComp_freePrefunctor_id q))
  refine (conj_eqToHom_iff_heq _ _ (hp _) (hp _)).1 ?_
  rw [comap_cell_of_grade_eq (Map.id P) ℓ hx hx hs ht]
  exact sandwich_eq (F := ℓ.toPrefunctor) _ _ _ (pathComp_freePrefunctor_id (P := P) _)
    (pathComp_freePrefunctor_id (P := P) _).symm _ _

private theorem isSandwich_comap_cell (f : Map P Q) (ℓ : Labelling B Q hQ) {x : P}
    (hx : grade ℕ x = 2) (h2 : grade ℕ (f x) = 2) {s t : P}
    (hs : P.boundary (.Iic x) 0 false = .Iic s) (ht : P.boundary (.Iic x) 0 true = .Iic t) :
    IsSandwich ℓ.toPrefunctor (pathComp f.freePrefunctor (boundaryPath P hP x false hs ht))
      (pathComp f.freePrefunctor (boundaryPath P hP x true hs ht))
      (ℓ.cell (f x) h2 (f.boundary_Iic_apply hs) (f.boundary_Iic_apply ht))
      ((ℓ.comap f hP).cell x hx hs ht) :=
  ⟨_, _, _, _, comap_cell_of_grade_eq f ℓ hx h2 hs ht⟩

private theorem isStructural_comap_cell (f : Map P Q) (ℓ : Labelling B Q hQ) {x : P}
    (hx : grade ℕ x = 2) (h2 : grade ℕ (f x) ≠ 2) {s t : P}
    (hs : P.boundary (.Iic x) 0 false = .Iic s) (ht : P.boundary (.Iic x) 0 true = .Iic t) :
    IsStructural ℓ.toPrefunctor (pathComp f.freePrefunctor (boundaryPath P hP x false hs ht))
      (pathComp f.freePrefunctor (boundaryPath P hP x true hs ht))
      ((ℓ.comap f hP).cell x hx hs ht) :=
  have ⟨θ, h⟩ := comap_cell_of_grade_ne f ℓ hx h2 hs ht
  ⟨θ, _, _, h⟩

theorem comap_comp {R : OGP.{u''}} [Fintype R] [DecidableLE R] {hR : R.IsRDC} (g : Map Q R)
    (f : Map P Q) (ℓ : Labelling B R hR) :
    ℓ.comap (g.comp f) hP = (ℓ.comap g hQ).comap f hP := by
  have hr {s t : P} (q : Quiver.Path (V := EdgeQuiver P) s t) :
      (lift g.freePrefunctor).map (pathComp f.freePrefunctor q) =
        pathComp (g.comp f).freePrefunctor q :=
    f.lift_map_pathComp_freePrefunctor g q
  have hp {s t : P} (q : Quiver.Path (V := EdgeQuiver P) s t) :
      pathComp (ℓ.comap (g.comp f) hP).toPrefunctor q =
        pathComp ((ℓ.comap g hQ).comap f hP).toPrefunctor q :=
    (pathComp_comp_lift _ _ q).trans ((congrArg _ (hr q)).symm.trans
      ((lift_map_lift _ _ _).symm.trans (pathComp_comp_lift _ _ q).symm))
  refine ext (Prefunctor.ext (fun _ => rfl) fun v w e => ?_) fun x hx s t hs ht => ?_
  · exact (congrArg _ (f.lift_map_freePrefunctor_map g e)).symm.trans (lift_map_lift _ _ _).symm
  refine (conj_eqToHom_iff_heq _ _ (hp _) (hp _)).1 ?_
  have hX := hr (boundaryPath P hP x false hs ht)
  have hY := hr (boundaryPath P hP x true hs ht)
  have hU (q : Quiver.Path (V := EdgeQuiver P) s t) :
      pathComp (ℓ.comap (g.comp f) hP).toPrefunctor q =
        (lift ℓ.toPrefunctor).map (pathComp (g.comp f).freePrefunctor q) :=
    pathComp_comp_lift _ _ q
  have hU' (q : Quiver.Path (V := EdgeQuiver P) s t) :
      pathComp ((ℓ.comap g hQ).comap f hP).toPrefunctor q =
        (lift ℓ.toPrefunctor).map (pathComp (g.comp f).freePrefunctor q) :=
    (hp q).symm.trans (hU q)
  by_cases h₁ : grade ℕ (f x) = 2
  · obtain ⟨θ₁, θ₂, hV, hV', hφ⟩ := isSandwich_comap_cell (hP := hP) f (ℓ.comap g hQ) hx h₁ hs ht
    by_cases h₂ : grade ℕ (g (f x)) = 2
    · have hC := isSandwich_comap_cell (hP := hQ) g ℓ h₁ h₂ (f.boundary_Iic_apply hs)
        (f.boundary_Iic_apply ht)
      have h₃ : IsSandwich ℓ.toPrefunctor
          (pathComp (g.comp f).freePrefunctor (boundaryPath P hP x false hs ht))
          (pathComp (g.comp f).freePrefunctor (boundaryPath P hP x true hs ht))
          (ℓ.cell (g (f x)) h₂ (g.boundary_Iic_apply (f.boundary_Iic_apply hs))
            (g.boundary_Iic_apply (f.boundary_Iic_apply ht)))
          (((ℓ.comap g hQ).comap f hP).cell x hx hs ht) := by
        rw [hφ]
        have h₁ := (isStructural_map₂ (F := g.freePrefunctor ⋙q (lift ℓ.toPrefunctor).toPrefunctor)
          θ₁).of_comp_lift
        have h₂ := (isStructural_map₂ (F := g.freePrefunctor ⋙q (lift ℓ.toPrefunctor).toPrefunctor)
          θ₂).of_comp_lift
        exact ((isSandwich_comp_comp (F := ℓ.toPrefunctor) hV h₁ hC h₂ hV').congr hX hY)
      exact (isSandwich_comap_cell (hP := hP) (g.comp f) ℓ hx h₂ hs ht).eq
        ((h₃.comp_eqToHom _).eqToHom_comp _)
    · have hC := isStructural_comap_cell (hP := hQ) g ℓ h₁ h₂ (f.boundary_Iic_apply hs)
        (f.boundary_Iic_apply ht)
      have h₃ : IsStructural ℓ.toPrefunctor
          (pathComp (g.comp f).freePrefunctor (boundaryPath P hP x false hs ht))
          (pathComp (g.comp f).freePrefunctor (boundaryPath P hP x true hs ht))
          (((ℓ.comap g hQ).comap f hP).cell x hx hs ht) := by
        rw [hφ]
        have h₁ := (isStructural_map₂ (F := g.freePrefunctor ⋙q (lift ℓ.toPrefunctor).toPrefunctor)
          θ₁).of_comp_lift
        have h₂ := (isStructural_map₂ (F := g.freePrefunctor ⋙q (lift ℓ.toPrefunctor).toPrefunctor)
          θ₂).of_comp_lift
        exact ((isStructural_comp_comp (F := ℓ.toPrefunctor) hV h₁ hC h₂ hV').congr hX hY)
      exact (isStructural_comap_cell (hP := hP) (g.comp f) ℓ hx h₂ hs ht).eq
        ((h₃.comp_eqToHom _).eqToHom_comp _)
  · have h₂ : grade ℕ ((g.comp f) x) ≠ 2 := by
      have := g.isMap_coe.grade_le (f x)
      have := f.isMap_coe.grade_le x
      rw [Map.comp_apply]
      omega
    obtain ⟨θ, hV, hV', hφ⟩ := isStructural_comap_cell (hP := hP) f (ℓ.comap g hQ) hx h₁ hs ht
    have h₃ : IsStructural ℓ.toPrefunctor
        (pathComp (g.comp f).freePrefunctor (boundaryPath P hP x false hs ht))
        (pathComp (g.comp f).freePrefunctor (boundaryPath P hP x true hs ht))
        (((ℓ.comap g hQ).comap f hP).cell x hx hs ht) := by
      rw [hφ]
      have h₁ := (isStructural_map₂ (F := g.freePrefunctor ⋙q (lift ℓ.toPrefunctor).toPrefunctor)
        θ).of_comp_lift
      exact (IsStructural.eqToHom_comp (F := ℓ.toPrefunctor) hV
        (IsStructural.comp_eqToHom (F := ℓ.toPrefunctor) h₁ hV')).congr hX hY
    exact (isStructural_comap_cell (hP := hP) (g.comp f) ℓ hx h₂ hs ht).eq
      ((h₃.comp_eqToHom _).eqToHom_comp _)
private theorem isSandwich_whisker_cell (ℓ : Labelling B Q hQ) {z z' : Q} (hz : grade ℕ z = 2)
    (hz' : grade ℕ z' = 2) (e : z = z') {a b s t : Q} (ha : Q.boundary (.Iic z) 0 false = .Iic a)
    (hb : Q.boundary (.Iic z) 0 true = .Iic b) (hs : Q.boundary (.Iic z') 0 false = .Iic s)
    (ht : Q.boundary (.Iic z') 0 true = .Iic t)
    {Xp : Quiver.Hom (V := FreeBicategory (EdgeQuiver Q)) s a}
    {Xr : Quiver.Hom (V := FreeBicategory (EdgeQuiver Q)) b t}
    (hp : (normalizeAux .nil Xp).length = 0) (hr : (normalizeAux .nil Xr).length = 0) :
    IsSandwich ℓ.toPrefunctor (Xp ≫ inclusionPathAux (boundaryPath Q hQ z false ha hb) ≫ Xr)
      (Xp ≫ inclusionPathAux (boundaryPath Q hQ z true ha hb) ≫ Xr)
      (X' := inclusionPathAux (boundaryPath Q hQ z' false hs ht))
      (Y' := inclusionPathAux (boundaryPath Q hQ z' true hs ht)) (ℓ.cell z' hz' hs ht)
      ((lift ℓ.toPrefunctor).map Xp ◁ (ℓ.cell z hz ha hb ▷ (lift ℓ.toPrefunctor).map Xr)) := by
  subst e
  obtain rfl : a = s := LowerSet.Iic_injective (ha.symm.trans hs)
  obtain rfl : b = t := LowerSet.Iic_injective (hb.symm.trans ht)
  exact isSandwich_whisker_of_nil (Quiver.Path.eq_nil_of_length_zero _ hp)
    (Quiver.Path.eq_nil_of_length_zero _ hr) _

private theorem isStructural_layerComp (f : Map P Q) (ℓ : Labelling B Q hQ) {M : LowerSet P}
    [DecidablePred (· ∈ M)] (hM : IsMoleculeIn P M) {xs : List P} (h : IsLayerOrder M xs)
    {s t : P} (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t) {j : ℕ}
    (hj : j < xs.length) (h2 : grade ℕ (f xs[j]) ≠ 2) :
    IsStructural ℓ.toPrefunctor (pathComp f.freePrefunctor (stagePath hM h hs ht j))
      (pathComp f.freePrefunctor (stagePath hM h hs ht (j + 1)))
      ((ℓ.comap f hP).layerComp hM h hs ht j hj) := by
  have ha := boundary_zero_eq_Iic_vertex _ (hP xs[j]) false
  have hb := boundary_zero_eq_Iic_vertex _ (hP xs[j]) true
  obtain ⟨p, c, e⟩ := h.exists_stagePath_eq hs ht hM hj ha hb
  have e' := h.comp_comp_eq_stagePath hs ht hM hj rfl (hP xs[j]) ha hb p c e
  rw [(ℓ.comap f hP).layerComp_eq hM h hs ht hj rfl ha hb p c e e']
  exact (((isStructural_pathWhisker p c (isStructural_comap_cell (hP := hP) f ℓ
    (h.grade_eq _ (List.getElem_mem hj)) h2 ha hb)).comp_eqToHom _).eqToHom_comp _).congr
      (congrArg _ e).symm (congrArg _ e')

private theorem isSandwich_layerComp (f : Map P Q) (ℓ : Labelling B Q hQ) {M : LowerSet P}
    [DecidablePred (· ∈ M)] (hM : IsMoleculeIn P M) {xs : List P} (h : IsLayerOrder M xs)
    {s t : P} (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t) {j : ℕ}
    (hj : j < xs.length) {z : Q} (hz : grade ℕ z = 2) (hfz : f xs[j] = z)
    (hs' : Q.boundary (.Iic z) 0 false = .Iic (f s)) (ht' : Q.boundary (.Iic z) 0 true = .Iic (f t))
    (hlen : (f.mapPath (stagePath hM h hs ht j)).length ≤
      (edgeList (Q.boundary (.Iic z) 1 false)).length) :
    IsSandwich ℓ.toPrefunctor (pathComp f.freePrefunctor (stagePath hM h hs ht j))
      (pathComp f.freePrefunctor (stagePath hM h hs ht (j + 1)))
      (X' := inclusionPathAux (boundaryPath Q hQ z false hs' ht'))
      (Y' := inclusionPathAux (boundaryPath Q hQ z true hs' ht')) (ℓ.cell z hz hs' ht')
      ((ℓ.comap f hP).layerComp hM h hs ht j hj) := by
  have ha := boundary_zero_eq_Iic_vertex _ (hP xs[j]) false
  have hb := boundary_zero_eq_Iic_vertex _ (hP xs[j]) true
  obtain ⟨p, c, e⟩ := h.exists_stagePath_eq hs ht hM hj ha hb
  have e' := h.comp_comp_eq_stagePath hs ht hM hj rfl (hP xs[j]) ha hb p c e
  have h2 : grade ℕ (f xs[j]) = 2 := hfz ▸ hz
  have hl : (f.mapPath p).length + (edgeList (Q.boundary (.Iic z) 1 false)).length +
      (f.mapPath c).length ≤ (edgeList (Q.boundary (.Iic z) 1 false)).length := by
    have hm := congrArg Quiver.Path.length (congrArg f.mapPath e)
    rw [f.mapPath_comp, f.mapPath_comp, Quiver.Path.length_comp, Quiver.Path.length_comp,
      f.mapPath_pathOf_boundary hP hQ xs[j] false, length_pathOf, hfz] at hm
    omega
  have hp : (f.mapPath p).length = 0 := by omega
  have hc : (f.mapPath c).length = 0 := by omega
  rw [(ℓ.comap f hP).layerComp_eq hM h hs ht hj rfl ha hb p c e e']
  have hw := (isSandwich_pathWhisker p c (isSandwich_comap_cell (hP := hP) f ℓ
    (h.grade_eq _ (List.getElem_mem hj)) h2 ha hb)).trans (isSandwich_whisker_cell ℓ h2 hz hfz
      (f.boundary_Iic_apply ha) (f.boundary_Iic_apply hb) hs' ht'
      ((congrArg Quiver.Path.length (f.normalizeAux_nil_pathComp_freePrefunctor p)).trans hp)
      ((congrArg Quiver.Path.length (f.normalizeAux_nil_pathComp_freePrefunctor c)).trans hc))
  exact ((hw.comp_eqToHom _).eqToHom_comp _).congr (congrArg _ e).symm (congrArg _ e')

private theorem isStructural_compositeUpTo (f : Map P Q) (ℓ : Labelling B Q hQ) {M : LowerSet P}
    [DecidablePred (· ∈ M)] (hM : IsMoleculeIn P M) {xs : List P} (h : IsLayerOrder M xs)
    {s t : P} (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t) :
    ∀ (n : ℕ) (hn : n ≤ xs.length),
      (∀ (j : ℕ) (hj : j < n), grade ℕ (f (xs[j]'(lt_of_lt_of_le hj hn))) ≠ 2) →
      IsStructural ℓ.toPrefunctor (pathComp f.freePrefunctor (stagePath hM h hs ht 0))
        (pathComp f.freePrefunctor (stagePath hM h hs ht n))
        ((ℓ.comap f hP).compositeUpTo hM h hs ht n hn)
  | 0, _, _ => isStructural_id (pathComp_comp_lift _ _ _)
  | n + 1, hn, hc => by
    rw [Labelling.compositeUpTo_succ]
    exact (isStructural_compositeUpTo f ℓ hM h hs ht n (by omega) fun j hj => hc j (by omega)).comp
      (isStructural_layerComp f ℓ hM h hs ht _ (hc n (by omega)))

private theorem isSandwich_compositeUpTo (f : Map P Q) (ℓ : Labelling B Q hQ) {M : LowerSet P}
    [DecidablePred (· ∈ M)] (hM : IsMoleculeIn P M) {xs : List P} (h : IsLayerOrder M xs)
    {s t : P} (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t) {k : ℕ}
    (hk : k < xs.length) {z : Q} (hz : grade ℕ z = 2) (hfz : f xs[k] = z)
    (hs' : Q.boundary (.Iic z) 0 false = .Iic (f s)) (ht' : Q.boundary (.Iic z) 0 true = .Iic (f t))
    (hlen : (f.mapPath (stagePath hM h hs ht k)).length ≤
      (edgeList (Q.boundary (.Iic z) 1 false)).length) :
    ∀ (n : ℕ) (hn : n ≤ xs.length), k < n →
      (∀ (j : ℕ) (hj : j < n), j ≠ k → grade ℕ (f (xs[j]'(lt_of_lt_of_le hj hn))) ≠ 2) →
      IsSandwich ℓ.toPrefunctor (pathComp f.freePrefunctor (stagePath hM h hs ht 0))
        (pathComp f.freePrefunctor (stagePath hM h hs ht n))
        (X' := inclusionPathAux (boundaryPath Q hQ z false hs' ht'))
        (Y' := inclusionPathAux (boundaryPath Q hQ z true hs' ht')) (ℓ.cell z hz hs' ht')
        ((ℓ.comap f hP).compositeUpTo hM h hs ht n hn)
  | 0, _, hkn, _ => absurd hkn (Nat.not_lt_zero _)
  | n + 1, hn, hkn, hc => by
    rw [Labelling.compositeUpTo_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hkn with hkn | rfl
    · exact (isSandwich_compositeUpTo f ℓ hM h hs ht hk hz hfz hs' ht' hlen n (by omega) hkn
        fun j hj hjk => hc j (by omega) hjk).comp_isStructural
          (isStructural_layerComp f ℓ hM h hs ht _ (hc n (by omega) (by omega)))
    · exact (isStructural_compositeUpTo f ℓ hM h hs ht _ (by omega)
        fun j hj => hc j (by omega) (by omega)).comp_isSandwich
          (isSandwich_layerComp f ℓ hM h hs ht hk hz hfz hs' ht' hlen)

private theorem mapPath_stagePath (hP : P.IsRDC) (hQ : Q.IsRDC) (f : Map P Q) {M : LowerSet P}
    [DecidablePred (· ∈ M)] (hM : IsMoleculeIn P M) {xs : List P} (h : IsLayerOrder M xs) {s t : P}
    (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t)
    {U : LowerSet Q} [DecidablePred (· ∈ U)] {hU : IsMoleculeIn Q U} {hd : krullDim U ≤ 1}
    {hv : Q.boundary U 0 false = .Iic (f s)} {hw : Q.boundary U 0 true = .Iic (f t)}
    (h0 : f.mapPath (stagePath hM h hs ht 0) = pathOf U hU hd hv hw) :
    ∀ (n : ℕ) (hn : n ≤ xs.length),
      (∀ (j : ℕ) (hj : j < n), grade ℕ (f (xs[j]'(lt_of_lt_of_le hj hn))) ≠ 2) →
      f.mapPath (stagePath hM h hs ht n) = pathOf U hU hd hv hw
  | 0, _, _ => h0
  | n + 1, hn, hc => by
    have ha := boundary_zero_eq_Iic_vertex _ (hP xs[n]) false
    have hb := boundary_zero_eq_Iic_vertex _ (hP xs[n]) true
    obtain ⟨p, c, e⟩ := h.exists_stagePath_eq hs ht hM (j := n) (by omega) ha hb
    have e' := h.comp_comp_eq_stagePath hs ht hM (j := n) (by omega) rfl (hP xs[n]) ha hb p c e
    have hle : grade ℕ (f xs[n]) ≤ 1 := by
      have := f.isMap_coe.grade_le xs[n]
      rw [h.grade_eq _ (List.getElem_mem _)] at this
      have := hc n (by omega)
      omega
    have h₁ := f.mapPath_pathOf_boundary hP hQ xs[n] false
      (((hP xs[n]).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ha)
      (((hP xs[n]).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hb)
    have h₂ := f.mapPath_pathOf_boundary hP hQ xs[n] true
      (((hP xs[n]).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ha)
      (((hP xs[n]).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hb)
    have h₃ := boundaryPath_false_eq_true Q hQ hle (f.boundary_Iic_apply ha)
      (f.boundary_Iic_apply hb)
    calc f.mapPath (stagePath hM h hs ht (n + 1))
        = (f.mapPath p).comp ((f.mapPath (pathOf (P.boundary (.Iic xs[n]) 1 true)
            ((hP xs[n]).boundary 1 true) ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
            (((hP xs[n]).isGlobular.boundary_boundary_eq_of_le zero_le_one
              (.inl zero_lt_one)).trans ha)
            (((hP xs[n]).isGlobular.boundary_boundary_eq_of_le zero_le_one
              (.inl zero_lt_one)).trans hb))).comp (f.mapPath c)) := by
          rw [← e', f.mapPath_comp, f.mapPath_comp]
      _ = f.mapPath (stagePath hM h hs ht n) := by
          rw [e, f.mapPath_comp, f.mapPath_comp]
          exact congrArg (fun r => (f.mapPath p).comp (r.comp (f.mapPath c)))
            (h₂.trans (h₃.symm.trans h₁.symm))
      _ = pathOf U hU hd hv hw :=
          mapPath_stagePath hP hQ f hM h hs ht h0 n (by omega) fun j hj => hc j (by omega)

theorem isStructural_compositeAlong (f : Map P Q) (ℓ : Labelling B Q hQ) {M : LowerSet P}
    [DecidablePred (· ∈ M)] (hM : IsMoleculeIn P M) {xs : List P} (h : IsLayerOrder M xs)
    {s t : P} (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t)
    (hc : ∀ (j : ℕ) (hj : j < xs.length), grade ℕ (f xs[j]) ≠ 2) :
    IsStructural ℓ.toPrefunctor (pathComp f.freePrefunctor (pathOf (P.boundary M 1 false)
        (hM.boundary 1 false) ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)))
      (pathComp f.freePrefunctor (pathOf (P.boundary M 1 true) (hM.boundary 1 true)
        ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)))
      ((ℓ.comap f hP).compositeAlong hM h hs ht) := by
  rw [Labelling.compositeAlong]
  exact (((isStructural_compositeUpTo f ℓ hM h hs ht _ le_rfl hc).comp_eqToHom _).eqToHom_comp
    _).congr (congrArg _ (stagePath_zero hM h hs ht)) (congrArg _ (stagePath_length hM h hs ht))

theorem isSandwich_compositeAlong (f : Map P Q) (ℓ : Labelling B Q hQ) {M : LowerSet P}
    [DecidablePred (· ∈ M)] (hM : IsMoleculeIn P M) {xs : List P} (h : IsLayerOrder M xs)
    {s t : P} (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t) {k : ℕ}
    (hk : k < xs.length) {z : Q} (hz : grade ℕ z = 2) (hfz : f xs[k] = z)
    (hs' : Q.boundary (.Iic z) 0 false = .Iic (f s)) (ht' : Q.boundary (.Iic z) 0 true = .Iic (f t))
    (hlen : (f.mapPath (stagePath hM h hs ht k)).length ≤
      (edgeList (Q.boundary (.Iic z) 1 false)).length)
    (hc : ∀ (j : ℕ) (hj : j < xs.length), j ≠ k → grade ℕ (f xs[j]) ≠ 2) :
    IsSandwich ℓ.toPrefunctor (pathComp f.freePrefunctor (pathOf (P.boundary M 1 false)
        (hM.boundary 1 false) ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)))
      (pathComp f.freePrefunctor (pathOf (P.boundary M 1 true) (hM.boundary 1 true)
        ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)))
      (X' := inclusionPathAux (pathOf (Q.boundary (.Iic z) 1 false) ((hQ z).boundary 1 false)
        ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
        (((hQ z).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs')
        (((hQ z).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht')))
      (Y' := inclusionPathAux (pathOf (Q.boundary (.Iic z) 1 true) ((hQ z).boundary 1 true)
        ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        (((hQ z).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs')
        (((hQ z).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht')))
      (ℓ.cell z hz hs' ht') ((ℓ.comap f hP).compositeAlong hM h hs ht) := by
  rw [Labelling.compositeAlong]
  exact (((isSandwich_compositeUpTo f ℓ hM h hs ht hk hz hfz hs' ht' hlen _ le_rfl hk
    hc).comp_eqToHom _).eqToHom_comp _).congr (congrArg _ (stagePath_zero hM h hs ht))
      (congrArg _ (stagePath_length hM h hs ht))

private theorem IsLayerOrder.getElem_injective {R : OGP.{u''}} {M : LowerSet R} {xs : List R}
    (h : IsLayerOrder M xs) {i j : ℕ} (hi : i < xs.length) (hj : j < xs.length)
    (e : xs[i] = xs[j]) : i = j := by
  have key {i j : ℕ} (hi : i < xs.length) (hj : j < xs.length) (hij : i < j) :
      xs[i] ≠ xs[j] := fun e => by
    have hm : xs[i] ∈ xs.take (i + 1) :=
      List.mem_iff_getElem.2 ⟨i, by rw [List.length_take]; omega, List.getElem_take⟩
    refine h.getElem_notMem_orderPrefix hj (orderPrefix_mono (M := M) (xs := xs) (j := i + 1)
      (k := j) hij (mem_orderPrefix.2 (.inr ⟨xs[i], hm, ?_⟩)))
    rw [e]
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact (key hi hj hij e).elim
  · rfl
  · exact (key hj hi hij e.symm).elim

def IsCommutativeAt (ℓ : Labelling B P hP) (y : P) : Prop :=
  ∀ {s t : P} (hs : P.boundary (.Iic y) 0 false = .Iic s)
    (ht : P.boundary (.Iic y) 0 true = .Iic t) {xs ys : List P}
    (hxs : IsLayerOrder (P.boundary (.Iic y) 2 false) xs)
    (hys : IsLayerOrder (P.boundary (.Iic y) 2 true) ys),
    eqToHom (congrArg (pathComp ℓ.toPrefunctor) (pathOf_congr (hU := (hP y).boundary 1 false)
        (hd := (krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
        (hv := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          hs)
        (hw := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          ht)
        ((hP y).isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two)).symm)) ≫
      ℓ.compositeAlong ((hP y).boundary 2 false) hxs
        (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans hs)
        (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans ht) ≫
      eqToHom (congrArg (pathComp ℓ.toPrefunctor) (pathOf_congr
        (hU := ((hP y).boundary 2 false).boundary 1 true)
        (hd := (krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        (hV := (hP y).boundary 1 true)
        (hdV := (krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        (hv' := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          hs)
        (hw' := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          ht)
        ((hP y).isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two)))) =
    eqToHom (congrArg (pathComp ℓ.toPrefunctor) (pathOf_congr (hU := (hP y).boundary 1 false)
        (hd := (krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
        (hv := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          hs)
        (hw := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          ht)
        ((hP y).isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two)).symm)) ≫
      ℓ.compositeAlong ((hP y).boundary 2 true) hys
        (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans hs)
        (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans ht) ≫
      eqToHom (congrArg (pathComp ℓ.toPrefunctor) (pathOf_congr
        (hU := ((hP y).boundary 2 true).boundary 1 true)
        (hd := (krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        (hV := (hP y).boundary 1 true)
        (hdV := (krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        (hv' := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          hs)
        (hw' := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          ht)
        ((hP y).isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two))))

def IsCommutative (ℓ : Labelling B P hP) : Prop :=
  ∀ y : P, grade ℕ y = 3 → ℓ.IsCommutativeAt y

omit [Fintype Q] [DecidableLE Q] in
private theorem pathComp_pathOf_boundary_boundary (f : Map P Q) (y : P) (α β : Bool) {s t : P}
    (hs : P.boundary (P.boundary (.Iic y) 2 α) 0 false = .Iic s)
    (ht : P.boundary (P.boundary (.Iic y) 2 α) 0 true = .Iic t)
    (hs' : P.boundary (.Iic y) 0 false = .Iic s) (ht' : P.boundary (.Iic y) 0 true = .Iic t) :
    pathComp f.freePrefunctor (pathOf (P.boundary (P.boundary (.Iic y) 2 α) 1 β)
      (((hP y).boundary 2 α).boundary 1 β) ((krullDim_boundary_le _ 1 β).trans_eq Nat.cast_one)
      ((((hP y).boundary 2 α).isGlobular.boundary_boundary_eq_of_le zero_le_one
        (.inl zero_lt_one)).trans hs)
      ((((hP y).boundary 2 α).isGlobular.boundary_boundary_eq_of_le zero_le_one
        (.inl zero_lt_one)).trans ht)) =
      pathComp f.freePrefunctor (boundaryPath P hP y β hs' ht') :=
  congrArg _ (pathOf_congr ((hP y).isGlobular.boundary_boundary_eq_of_le one_le_two
    (.inl one_lt_two)))

private theorem isStructural_side (f : Map P Q) (ℓ : Labelling B Q hQ) {y : P} {s t : P}
    (hs : P.boundary (.Iic y) 0 false = .Iic s) (ht : P.boundary (.Iic y) 0 true = .Iic t)
    (α : Bool) {zs : List P} (hzs : IsLayerOrder (P.boundary (.Iic y) 2 α) zs)
    (hc : ∀ (j : ℕ) (hj : j < zs.length), grade ℕ (f zs[j]) ≠ 2) :
    IsStructural ℓ.toPrefunctor (pathComp f.freePrefunctor (boundaryPath P hP y false hs ht))
      (pathComp f.freePrefunctor (boundaryPath P hP y true hs ht))
      (eqToHom (congrArg (pathComp (ℓ.comap f hP).toPrefunctor) (pathOf_congr
        (hU := (hP y).boundary 1 false)
        (hd := (krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
        (hv := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          hs)
        (hw := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          ht)
        ((hP y).isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two)).symm)) ≫
      (ℓ.comap f hP).compositeAlong ((hP y).boundary 2 α) hzs
        (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans hs)
        (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans ht) ≫
      eqToHom (congrArg (pathComp (ℓ.comap f hP).toPrefunctor) (pathOf_congr
        (hU := ((hP y).boundary 2 α).boundary 1 true)
        (hd := (krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        (hV := (hP y).boundary 1 true)
        (hdV := (krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        (hv' := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          hs)
        (hw' := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          ht)
        ((hP y).isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two))))) :=
  have hs₂ := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans hs
  have ht₂ := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans ht
  (((isStructural_compositeAlong f ℓ _ hzs hs₂ ht₂ hc).comp_eqToHom _).eqToHom_comp _).congr
    (pathComp_pathOf_boundary_boundary f y α false hs₂ ht₂ hs ht)
    (pathComp_pathOf_boundary_boundary f y α true hs₂ ht₂ hs ht)

private theorem isSandwich_side (f : Map P Q) (ℓ : Labelling B Q hQ) {y : P} {s t : P}
    (hs : P.boundary (.Iic y) 0 false = .Iic s) (ht : P.boundary (.Iic y) 0 true = .Iic t)
    (α : Bool) {zs : List P} (hzs : IsLayerOrder (P.boundary (.Iic y) 2 α) zs) {k : ℕ}
    (hk : k < zs.length) {z : Q} (hz : grade ℕ z = 2) (hfz : f zs[k] = z)
    (hs' : Q.boundary (.Iic z) 0 false = .Iic (f s)) (ht' : Q.boundary (.Iic z) 0 true = .Iic (f t))
    (hlen : (f.mapPath (stagePath ((hP y).boundary 2 α) hzs
      (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans hs)
      (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans ht)
      k)).length ≤ (edgeList (Q.boundary (.Iic z) 1 false)).length)
    (hc : ∀ (j : ℕ) (hj : j < zs.length), j ≠ k → grade ℕ (f zs[j]) ≠ 2) :
    IsSandwich ℓ.toPrefunctor (pathComp f.freePrefunctor (boundaryPath P hP y false hs ht))
      (pathComp f.freePrefunctor (boundaryPath P hP y true hs ht))
      (X' := inclusionPathAux (boundaryPath Q hQ z false hs' ht'))
      (Y' := inclusionPathAux (boundaryPath Q hQ z true hs' ht')) (ℓ.cell z hz hs' ht')
      (eqToHom (congrArg (pathComp (ℓ.comap f hP).toPrefunctor) (pathOf_congr
        (hU := (hP y).boundary 1 false)
        (hd := (krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
        (hv := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          hs)
        (hw := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          ht)
        ((hP y).isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two)).symm)) ≫
      (ℓ.comap f hP).compositeAlong ((hP y).boundary 2 α) hzs
        (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans hs)
        (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans ht) ≫
      eqToHom (congrArg (pathComp (ℓ.comap f hP).toPrefunctor) (pathOf_congr
        (hU := ((hP y).boundary 2 α).boundary 1 true)
        (hd := (krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        (hV := (hP y).boundary 1 true)
        (hdV := (krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        (hv' := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          hs)
        (hw' := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          ht)
        ((hP y).isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two))))) :=
  have hs₂ := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans hs
  have ht₂ := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans ht
  (((isSandwich_compositeAlong f ℓ _ hzs hs₂ ht₂ hk hz hfz hs' ht' hlen hc).comp_eqToHom
    _).eqToHom_comp _).congr (pathComp_pathOf_boundary_boundary f y α false hs₂ ht₂ hs ht)
    (pathComp_pathOf_boundary_boundary f y α true hs₂ ht₂ hs ht)

theorem isCommutativeAt_comap_of_grade_lt (f : Map P Q) (ℓ : Labelling B Q hQ) {y : P}
    (hfy : grade ℕ (f y) < 3) : (ℓ.comap f hP).IsCommutativeAt y := by
  intro s t hs ht xs ys hxs hys
  have hle (α : Bool) {zs : List P} (hzs : IsLayerOrder (P.boundary (.Iic y) 2 α) zs) (j : ℕ)
      (hj : j < zs.length) : f zs[j] ≤ f y :=
    f.isMap_coe.monotone (boundary_le _ _ _ (hzs.mem (List.getElem_mem hj)))
  by_cases h2 : grade ℕ (f y) = 2
  · have hsand (α : Bool) {zs : List P} (hzs : IsLayerOrder (P.boundary (.Iic y) 2 α) zs) :
        IsSandwich ℓ.toPrefunctor (pathComp f.freePrefunctor (boundaryPath P hP y false hs ht))
          (pathComp f.freePrefunctor (boundaryPath P hP y true hs ht))
          (X' := inclusionPathAux (boundaryPath Q hQ (f y) false (f.boundary_Iic_apply hs)
            (f.boundary_Iic_apply ht)))
          (Y' := inclusionPathAux (boundaryPath Q hQ (f y) true (f.boundary_Iic_apply hs)
            (f.boundary_Iic_apply ht)))
          (ℓ.cell (f y) h2 (f.boundary_Iic_apply hs) (f.boundary_Iic_apply ht))
          (eqToHom (congrArg (pathComp (ℓ.comap f hP).toPrefunctor) (pathOf_congr
        (hU := (hP y).boundary 1 false)
        (hd := (krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
        (hv := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          hs)
        (hw := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          ht)
        ((hP y).isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two)).symm)) ≫
      (ℓ.comap f hP).compositeAlong ((hP y).boundary 2 α) hzs
        (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans hs)
        (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans ht) ≫
      eqToHom (congrArg (pathComp (ℓ.comap f hP).toPrefunctor) (pathOf_congr
        (hU := ((hP y).boundary 2 α).boundary 1 true)
        (hd := (krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        (hV := (hP y).boundary 1 true)
        (hdV := (krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        (hv' := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          hs)
        (hw' := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          ht)
        ((hP y).isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two))))) := by
      obtain ⟨z₀, ⟨hz₀, hgz₀, hfz₀⟩, huniq⟩ := f.isMap_coe.existsUnique_mem_boundary_apply_eq y α
      rw [h2] at hz₀ hgz₀
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (hzs.mem_of_mem hz₀ hgz₀)
      have hc (j : ℕ) (hj : j < zs.length) (hjk : j ≠ k) : grade ℕ (f zs[j]) ≠ 2 := fun hj2 =>
        hjk (IsLayerOrder.getElem_injective hzs hj hk ((huniq zs[j]
          ⟨h2 ▸ hzs.mem (List.getElem_mem hj),
          (hzs.grade_eq _ (List.getElem_mem hj)).trans h2.symm,
          GradeOrder.eq_of_le_of_grade_le (hle α hzs j hj) (by rw [hj2, h2])⟩).trans
            (huniq zs[k] ⟨h2 ▸ hz₀, hgz₀.trans h2.symm, hfz₀⟩).symm))
      have hs₂ := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)
        (β := α)).trans hs
      have ht₂ := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)
        (β := α)).trans ht
      have h0 : f.mapPath (stagePath ((hP y).boundary 2 α) hzs hs₂ ht₂ 0) =
          boundaryPath Q hQ (f y) false (f.boundary_Iic_apply hs) (f.boundary_Iic_apply ht) :=
        (congrArg f.mapPath ((stagePath_zero ((hP y).boundary 2 α) hzs hs₂ ht₂).trans
          (pathOf_congr ((hP y).isGlobular.boundary_boundary_eq_of_le one_le_two
            (.inl one_lt_two))))).trans (f.mapPath_pathOf_boundary hP hQ y false
              (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
                hs)
              (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
                ht))
      have hlen := congrArg Quiver.Path.length (mapPath_stagePath hP hQ f _ hzs hs₂ ht₂ h0 k hk.le
        fun j hj => hc j (by omega) (by omega))
      rw [length_pathOf] at hlen
      exact isSandwich_side f ℓ hs ht α hzs hk h2 hfz₀ (f.boundary_Iic_apply hs)
        (f.boundary_Iic_apply ht) hlen.le hc
    exact (hsand false hxs).eq (hsand true hys)
  · have hc (α : Bool) {zs : List P} (hzs : IsLayerOrder (P.boundary (.Iic y) 2 α) zs) (j : ℕ)
        (hj : j < zs.length) : grade ℕ (f zs[j]) ≠ 2 := by
      have : grade ℕ (f zs[j]) ≤ grade ℕ (f y) := grade_mono (hle α hzs j hj)
      omega
    exact (isStructural_side f ℓ hs ht false hxs (hc false hxs)).eq
      (isStructural_side f ℓ hs ht true hys (hc true hys))

private theorem pathComp_stagePath_comap (f : Map P Q) (ℓ : Labelling B Q hQ) {M : LowerSet P}
    [DecidablePred (· ∈ M)] (hM : IsMoleculeIn P M) {xs : List P} (h : IsLayerOrder M xs)
    {s t : P} (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t)
    {M' : LowerSet Q} [DecidablePred (· ∈ M')] (hM' : IsMoleculeIn Q M')
    (h' : IsLayerOrder M' (xs.map f)) (hs' : Q.boundary M' 0 false = .Iic (f s))
    (ht' : Q.boundary M' 0 true = .Iic (f t)) (hgr : ∀ x ∈ M, grade ℕ (f x) = grade ℕ x)
    (hm : ∀ k ≤ xs.length, f.mapPath (stagePath hM h hs ht k) = stagePath hM' h' hs' ht' k)
    {k : ℕ} (hk : k ≤ xs.length) :
    pathComp (ℓ.comap f hP).toPrefunctor (stagePath hM h hs ht k) =
      pathComp ℓ.toPrefunctor (stagePath hM' h' hs' ht' k) := by
  have hcol : ∀ d ∈ pathEdges (stagePath hM h hs ht k), grade ℕ (f d) = 1 := by
    intro d hd
    rw [pathEdges_stagePath] at hd
    obtain ⟨hdS, hd1⟩ := (mem_edgeList_iff ((h.isMoleculeIn_orderPrefix hM k).boundary 1 true)
      ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)).1 hd
    rw [hgr d (h.orderPrefix_le k (boundary_le _ _ _ hdS)), hd1]
  exact (f.pathComp_freePrefunctor_comp_lift_of_forall ℓ.toPrefunctor _ hcol).trans
    (congrArg (pathComp ℓ.toPrefunctor) (hm k hk))

private theorem conj_layerComp_comap (f : Map P Q) (ℓ : Labelling B Q hQ) {M : LowerSet P}
    [DecidablePred (· ∈ M)] (hM : IsMoleculeIn P M) {xs : List P} (h : IsLayerOrder M xs)
    {s t : P} (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t)
    {M' : LowerSet Q} [DecidablePred (· ∈ M')] (hM' : IsMoleculeIn Q M')
    (h' : IsLayerOrder M' (xs.map f)) (hs' : Q.boundary M' 0 false = .Iic (f s))
    (ht' : Q.boundary M' 0 true = .Iic (f t)) (hgr : ∀ x ∈ M, grade ℕ (f x) = grade ℕ x)
    (hm : ∀ k ≤ xs.length, f.mapPath (stagePath hM h hs ht k) = stagePath hM' h' hs' ht' k)
    {j : ℕ} (hj : j < xs.length) :
    ConjEqToHom ((ℓ.comap f hP).layerComp hM h hs ht j hj)
      (ℓ.layerComp hM' h' hs' ht' j (by simpa using hj)) := by
  have hx2 : grade ℕ xs[j] = 2 := h.grade_eq _ (List.getElem_mem hj)
  have hfx2 : grade ℕ (f xs[j]) = 2 := (hgr _ (h.mem (List.getElem_mem hj))).trans hx2
  have ha := boundary_zero_eq_Iic_vertex _ (hP xs[j]) false
  have hb := boundary_zero_eq_Iic_vertex _ (hP xs[j]) true
  obtain ⟨p, c, e⟩ := h.exists_stagePath_eq hs ht hM hj ha hb
  have e' := h.comp_comp_eq_stagePath hs ht hM hj rfl (hP xs[j]) ha hb p c e
  have hcol (k : ℕ) : ∀ d ∈ pathEdges (stagePath hM h hs ht k), grade ℕ (f d) = 1 := by
    intro d hd
    rw [pathEdges_stagePath] at hd
    obtain ⟨hdS, hd1⟩ := (mem_edgeList_iff ((h.isMoleculeIn_orderPrefix hM k).boundary 1 true)
      ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)).1 hd
    rw [hgr d (h.orderPrefix_le k (boundary_le _ _ _ hdS)), hd1]
  have hcol' : ∀ d ∈ pathEdges (p.comp ((boundaryPath P hP xs[j] false ha hb).comp c)),
      grade ℕ (f d) = 1 := e ▸ hcol j
  have hcp : ∀ d ∈ pathEdges p, grade ℕ (f d) = 1 := fun d hd => hcol' d (by simp [hd])
  have hcc : ∀ d ∈ pathEdges c, grade ℕ (f d) = 1 := fun d hd => hcol' d (by simp [hd])
  have hd (β : Bool) := f.mapPath_pathOf_boundary hP hQ xs[j] β
    (((hP xs[j]).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ha)
    (((hP xs[j]).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hb)
  have hpe : f.mapPath (p.comp ((boundaryPath P hP xs[j] false ha hb).comp c)) = (f.mapPath p).comp
      ((boundaryPath Q hQ (f xs[j]) false (f.boundary_Iic_apply ha) (f.boundary_Iic_apply hb)).comp
        (f.mapPath c)) := by
    rw [f.mapPath_comp, f.mapPath_comp]
    exact congrArg (fun r => (f.mapPath p).comp (r.comp (f.mapPath c))) (hd false)
  have h₁ : stagePath hM' h' hs' ht' j =
      (f.mapPath p).comp ((boundaryPath Q hQ (f xs[j]) false (f.boundary_Iic_apply ha)
        (f.boundary_Iic_apply hb)).comp (f.mapPath c)) :=
    (hm j hj.le).symm.trans ((congrArg f.mapPath e).trans hpe)
  have h₂ : (f.mapPath p).comp ((boundaryPath Q hQ (f xs[j]) true (f.boundary_Iic_apply ha)
      (f.boundary_Iic_apply hb)).comp (f.mapPath c)) = stagePath hM' h' hs' ht' (j + 1) := by
    rw [← hm (j + 1) hj, ← e', f.mapPath_comp, f.mapPath_comp]
    exact congrArg (fun r => (f.mapPath p).comp (r.comp (f.mapPath c))) (hd true).symm
  rw [(ℓ.comap f hP).layerComp_eq hM h hs ht hj rfl ha hb p c e e',
    ℓ.layerComp_eq hM' h' hs' ht' _ (List.getElem_map _) (f.boundary_Iic_apply ha)
      (f.boundary_Iic_apply hb) _ _ h₁ h₂]
  have hX : pathComp f.freePrefunctor (p.comp ((boundaryPath P hP xs[j] false ha hb).comp c)) =
      pathComp FreeBicategory.of ((f.mapPath p).comp ((boundaryPath Q hQ (f xs[j]) false
        (f.boundary_Iic_apply ha) (f.boundary_Iic_apply hb)).comp (f.mapPath c))) :=
    (f.pathComp_freePrefunctor_of_forall _ hcol').trans (congrArg _ hpe)
  have hY : pathComp f.freePrefunctor (p.comp ((boundaryPath P hP xs[j] true ha hb).comp c)) =
      pathComp FreeBicategory.of ((f.mapPath p).comp ((boundaryPath Q hQ (f xs[j]) true
        (f.boundary_Iic_apply ha) (f.boundary_Iic_apply hb)).comp (f.mapPath c))) := by
    refine (f.pathComp_freePrefunctor_of_forall _ (e' ▸ hcol (j + 1))).trans (congrArg _ ?_)
    rw [f.mapPath_comp, f.mapPath_comp]
    exact congrArg (fun r => (f.mapPath p).comp (r.comp (f.mapPath c))) (hd true)
  have hL := (((isSandwich_pathWhisker p c (isSandwich_comap_cell (hP := hP) f ℓ hx2 hfx2 ha
    hb)).congr_whisker (f.pathComp_freePrefunctor_of_forall p hcp)
      (f.pathComp_freePrefunctor_of_forall c hcc)).congr hX hY)
  have hR := isSandwich_pathWhisker (G := FreeBicategory.of) (F := ℓ.toPrefunctor) (f.mapPath p)
    (f.mapPath c) (isSandwich_self (C := ℓ.cell (f xs[j]) hfx2 (f.boundary_Iic_apply ha)
      (f.boundary_Iic_apply hb)) (pathComp_of _) (pathComp_of _).symm)
  exact ⟨pathComp_stagePath_comap f ℓ hM h hs ht hM' h' hs' ht' hgr hm hj.le,
    (pathComp_stagePath_comap f ℓ hM h hs ht hM' h' hs' ht' hgr hm hj).symm,
    ((hL.comp_eqToHom _).eqToHom_comp _).eq
    ((((hR.comp_eqToHom _).eqToHom_comp _).comp_eqToHom _).eqToHom_comp _)⟩

private theorem conj_compositeAlong_comap (f : Map P Q) (ℓ : Labelling B Q hQ) {M : LowerSet P}
    [DecidablePred (· ∈ M)] (hM : IsMoleculeIn P M) {xs : List P} (h : IsLayerOrder M xs)
    {s t : P} (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t)
    {M' : LowerSet Q} [DecidablePred (· ∈ M')] (hM' : IsMoleculeIn Q M')
    (h' : IsLayerOrder M' (xs.map f)) (hs' : Q.boundary M' 0 false = .Iic (f s))
    (ht' : Q.boundary M' 0 true = .Iic (f t)) (hgr : ∀ x ∈ M, grade ℕ (f x) = grade ℕ x)
    (hm : ∀ k ≤ xs.length, f.mapPath (stagePath hM h hs ht k) = stagePath hM' h' hs' ht' k) :
    ConjEqToHom ((ℓ.comap f hP).compositeAlong hM h hs ht) (ℓ.compositeAlong hM' h' hs' ht') := by
  have key (n : ℕ) (hn : n ≤ xs.length) :
      ConjEqToHom ((ℓ.comap f hP).compositeUpTo hM h hs ht n hn)
        (ℓ.compositeUpTo hM' h' hs' ht' n (by simpa using hn)) := by
    induction n with
    | zero =>
      exact conjEqToHom_id (pathComp_stagePath_comap f ℓ hM h hs ht hM' h' hs' ht' hgr hm
        (Nat.zero_le _))
    | succ n ih =>
      rw [Labelling.compositeUpTo_succ, Labelling.compositeUpTo_succ]
      exact (ih (by omega)).comp (conj_layerComp_comap f ℓ hM h hs ht hM' h' hs' ht' hgr hm _)
  have hlen (n m : ℕ) (hnm : n = m) (hn : n ≤ (xs.map f).length) (hm : m ≤ (xs.map f).length) :
      ConjEqToHom (ℓ.compositeUpTo hM' h' hs' ht' n hn) (ℓ.compositeUpTo hM' h' hs' ht' m hm) := by
    subst hnm
    exact conjEqToHom_refl _
  rw [Labelling.compositeAlong, Labelling.compositeAlong]
  exact ((key _ le_rfl).trans (hlen _ _ (List.length_map _).symm _ le_rfl)).conj _ _ _ _

theorem IsCommutative.comap (f : Map P Q) [f.isMap.monotone.functor.IsFibered]
    {ℓ : Labelling B Q hQ} (h : ℓ.IsCommutative) : (ℓ.comap f hP).IsCommutative := by
  intro y hy
  by_cases h3 : grade ℕ (f y) = 3
  · obtain ⟨hinj, hgr⟩ := f.isMap.injOn_Iic_and_grade_apply_eq (h3.trans hy.symm)
    intro hs ht xs ys hxs hys
    have hs₂ (α : Bool) := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two
      (.inl two_pos) (β := α)).trans hs
    have ht₂ (α : Bool) := ((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two
      (.inl two_pos) (β := α)).trans ht
    have hs₂' (α : Bool) := ((hQ (f y)).isGlobular.boundary_boundary_eq_of_le zero_le_two
      (.inl two_pos) (β := α)).trans (f.boundary_Iic_apply hs)
    have ht₂' (α : Bool) := ((hQ (f y)).isGlobular.boundary_boundary_eq_of_le zero_le_two
      (.inl two_pos) (β := α)).trans (f.boundary_Iic_apply ht)
    have hc (α : Bool) {zs : List P} (hzs : IsLayerOrder (P.boundary (.Iic y) 2 α) zs) :=
      conj_compositeAlong_comap (hP := hP) f ℓ ((hP y).boundary 2 α) hzs (hs₂ α) (ht₂ α)
        ((hQ (f y)).boundary 2 α) (hzs.map_of_injOn f hP hQ hinj hgr) (hs₂' α) (ht₂' α)
        (fun x hx => hgr x (boundary_le _ _ _ hx))
        (fun _ hk => mapPath_stagePath_map f hP hQ hinj hgr hzs _ _ _ _ hk)
    exact ConjEqToHom.eq_of_eq ((hc false hxs).conj _ _ _ _) ((hc true hys).conj _ _ _ _)
      (h (f y) h3 (f.boundary_Iic_apply hs) (f.boundary_Iic_apply ht)
        (hxs.map_of_injOn f hP hQ hinj hgr) (hys.map_of_injOn f hP hQ hinj hgr))
  · exact isCommutativeAt_comap_of_grade_lt f ℓ (by
      have := f.isMap_coe.grade_le y
      omega)

end Labelling

end Atoms.Molecule.OGP

namespace Atoms.Molecule.OGP

variable {P Q : OGP.{u}}

section Inclusion

variable (f : P ⟶ Q) [IsInclusion f]

theorem map_orderPrefix (M : LowerSet P) (xs : List P) (j : ℕ) :
    map f (orderPrefix M xs j) = orderPrefix (map f M) (xs.map f) j := by
  refine SetLike.ext fun y => ?_
  rw [mem_orderPrefix, ← map_boundary, mem_map, mem_map, ← List.map_take]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases mem_orderPrefix.1 hx with hx | ⟨z, hz, hxz⟩
    · exact .inl ⟨x, hx, rfl⟩
    · exact .inr ⟨f z, List.mem_map_of_mem hz, (isMorphism f).monotone hxz⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨_, hfz, hyz⟩)
    · exact ⟨x, mem_orderPrefix.2 (.inl hx), rfl⟩
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hfz
      obtain ⟨x, hx, rfl⟩ : y ∈ map f (.Iic z) := by
        rw [map_Iic]
        exact hyz
      exact ⟨x, mem_orderPrefix.2 (.inr ⟨z, hz, hx⟩), rfl⟩

theorem IsLayerOrder.map_of_isInclusion {M : LowerSet P} {xs : List P}
    (h : IsLayerOrder M xs) : IsLayerOrder (map f M) (xs.map f) where
  grade_eq x hx := by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    rw [(isMorphism f).grade_eq, h.grade_eq z hz]
  Iic_inf_orderPrefix j hj := by
    rw [List.getElem_map, ← map_Iic, ← map_orderPrefix, ← map_inf,
      h.Iic_inf_orderPrefix j (by simpa using hj), map_boundary, map_Iic]
  isSubmoleculeOf j hj := by
    rw [List.getElem_map, ← map_Iic, ← map_orderPrefix, ← map_boundary, ← map_boundary]
    exact (isSubmoleculeOf_map_iff f).2 (h.isSubmoleculeOf j (by simpa using hj))
  orderPrefix_length := by
    rw [List.length_map, ← map_orderPrefix, h.orderPrefix_length]

end Inclusion

namespace Labelling

variable [Fintype P] [DecidableLE P] [Fintype Q] [DecidableLE Q] {B : Type u₁}
  [Bicategory.{w, v} B] {hP : P.IsRDC} {hQ : Q.IsRDC}

private theorem mapPath_stagePath_of_isInclusion (f : P ⟶ Q) [IsInclusion f] {M : LowerSet P}
    [DecidablePred (· ∈ M)] [DecidablePred (· ∈ map f M)] (hM : IsMoleculeIn P M) {xs : List P}
    (h : IsLayerOrder M xs) {s t : P} (hs : P.boundary M 0 false = .Iic s)
    (ht : P.boundary M 0 true = .Iic t) (k : ℕ) :
    (⟨f, isMap_of_isInclusion f⟩ : Map P Q).mapPath (stagePath hM h hs ht k) =
      stagePath ((isMoleculeIn_map_iff f M).2 hM) (h.map_of_isInclusion f)
        ((map_boundary f M 0 false).symm.trans ((congrArg (map f) hs).trans (map_Iic f s)))
        ((map_boundary f M 0 true).symm.trans ((congrArg (map f) ht).trans (map_Iic f t))) k := by
  refine eq_stagePath_of_forall_mem _ _ _ _ _ fun e he => ?_
  obtain ⟨d, hd, rfl⟩ := Map.exists_mem_pathEdges_of_mem_pathEdges_mapPath _ _ he
  rw [pathEdges_stagePath] at hd
  have hd' := ((mem_edgeList_iff ((h.isMoleculeIn_orderPrefix hM k).boundary 1 true)
    ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)).1 hd).1
  have hfd : f d ∈ Q.boundary (orderPrefix (map f M) (xs.map f) k) 1 true := by
    rw [← map_orderPrefix, ← map_boundary]
    exact ⟨d, hd', rfl⟩
  exact hfd

theorem compositeAlong_comap_of_isInclusion (f : P ⟶ Q) [IsInclusion f] (ℓ : Labelling B Q hQ)
    {M : LowerSet P} [DecidablePred (· ∈ M)] [DecidablePred (· ∈ map f M)]
    (hM : IsMoleculeIn P M) {xs : List P} (h : IsLayerOrder M xs) {s t : P}
    (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t) :
    ConjEqToHom ((ℓ.comap ⟨f, isMap_of_isInclusion f⟩ hP).compositeAlong hM h hs ht)
      (ℓ.compositeAlong ((isMoleculeIn_map_iff f M).2 hM) (h.map_of_isInclusion f)
        ((map_boundary f M 0 false).symm.trans ((congrArg (map f) hs).trans (map_Iic f s)))
        ((map_boundary f M 0 true).symm.trans ((congrArg (map f) ht).trans (map_Iic f t)))) :=
  conj_compositeAlong_comap _ ℓ hM h hs ht _ (h.map_of_isInclusion f) _ _
    (fun x _ => (isMorphism f).grade_eq x)
    (fun k _ => mapPath_stagePath_of_isInclusion f hM h hs ht k)

theorem _root_.Atoms.Molecule.OGP.Map.mapPath_pathOf_of_isInclusion (f : P ⟶ Q) [IsInclusion f]
    (U : LowerSet P) [DecidablePred (· ∈ U)] [DecidablePred (· ∈ map f U)]
    (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) {v w : P} (hv : P.boundary U 0 false = .Iic v)
    (hw : P.boundary U 0 true = .Iic w) :
    (⟨f, isMap_of_isInclusion f⟩ : Map P Q).mapPath (pathOf U hU hd hv hw) =
      pathOf (map f U) ((isMoleculeIn_map_iff f U).2 hU) ((krullDim_map f U).trans_le hd)
        ((map_boundary f U 0 false).symm.trans ((congrArg (map f) hv).trans (map_Iic f v)))
        ((map_boundary f U 0 true).symm.trans ((congrArg (map f) hw).trans (map_Iic f w))) := by
  refine eq_pathOf_of_forall_mem _ _ _ _ _ fun e he => ?_
  obtain ⟨d, hd', rfl⟩ := Map.exists_mem_pathEdges_of_mem_pathEdges_mapPath _ _ he
  rw [pathEdges_pathOf] at hd'
  exact ⟨d, ((mem_edgeList_iff hU hd).1 hd').1, rfl⟩

omit [Fintype P] [DecidableLE P] [Fintype Q] [DecidableLE Q] in
theorem _root_.Atoms.Molecule.OGP.Map.pathComp_freePrefunctor_mapPath_of_isInclusion
    {R : OGP.{u}} (f : P ⟶ Q) [IsInclusion f] (g : Map Q R) {a b : EdgeQuiver P}
    (p : Quiver.Path a b) :
    pathComp g.freePrefunctor ((⟨f, isMap_of_isInclusion f⟩ : Map P Q).mapPath p) =
      pathComp (g.comp ⟨f, isMap_of_isInclusion f⟩).freePrefunctor p :=
  (pathComp_comp_lift FreeBicategory.of g.freePrefunctor _).trans
    ((congrArg (lift g.freePrefunctor).map
      ((⟨f, isMap_of_isInclusion f⟩ : Map P Q).pathComp_freePrefunctor_of_forall p
        fun e he => ((isMorphism f).grade_eq e).trans (grade_of_mem_pathEdges p he))).symm.trans
      ((⟨f, isMap_of_isInclusion f⟩ : Map P Q).lift_map_pathComp_freePrefunctor g p))

theorem pathCell_congr (ℓ : Labelling B P hP) {M M' : LowerSet P} [d : DecidablePred (· ∈ M)]
    [d' : DecidablePred (· ∈ M')] (e : M = M') (hM : IsMoleculeIn P M)
    (hM' : IsMoleculeIn P M') {xs ys : List P} (hxs : IsLayerOrder M xs)
    (hys : IsLayerOrder M' ys) {s t s' t' : P} (hs : P.boundary M 0 false = .Iic s)
    (ht : P.boundary M 0 true = .Iic t) (hs' : P.boundary M' 0 false = .Iic s')
    (ht' : P.boundary M' 0 true = .Iic t') :
    ℓ.pathCell hM hxs hs ht = ℓ.pathCell hM' hys hs' ht' := by
  subst e
  obtain rfl : d = d' := Subsingleton.elim _ _
  obtain rfl : s = s' := LowerSet.Iic_injective (hs.symm.trans hs')
  obtain rfl : t = t' := LowerSet.Iic_injective (ht.symm.trans ht')
  simp only [pathCell, ℓ.compositeAlong_eq hM hs ht hxs hys]

theorem pathCell_of_krullDim_le_one (ℓ : Labelling B P hP) {M : LowerSet P}
    [DecidablePred (· ∈ M)] (hM : IsMoleculeIn P M) {xs : List P} (h : IsLayerOrder M xs)
    {s t : P} (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t)
    (hd : krullDim M ≤ 1) :
    ℓ.pathCell hM h hs ht = ⟨_, _, ℓ.toPrefunctor.mapPath (pathOf M hM hd hs ht),
      ℓ.toPrefunctor.mapPath (pathOf M hM hd hs ht), 𝟙 _⟩ := by
  rw [ℓ.pathCell_congr rfl hM hM h (isLayerOrder_nil hd) hs ht hs ht]
  have hb (α : Bool) : pathOf (P.boundary M 1 α) (hM.boundary 1 α)
      ((krullDim_boundary_le _ 1 α).trans_eq Nat.cast_one)
      ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
      ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht) =
      pathOf M hM hd hs ht := pathOf_congr (boundary_eq_self hd α)
  refine PathCell.ext rfl rfl (heq_of_eq (congrArg _ (hb false)))
    (heq_of_eq (congrArg _ (hb true))) ?_
  refine (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans ?_)
  refine (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans ?_)
  exact (conjEqToHom_id
    (X := pathComp ℓ.toPrefunctor (stagePath hM (isLayerOrder_nil hd) hs ht 0))
    (by rw [stagePath_zero, hb false, pathComp_mapPath])).heq

theorem pathCell_comap_of_isInclusion (f : P ⟶ Q) [IsInclusion f] (ℓ : Labelling B Q hQ)
    {M : LowerSet P} [DecidablePred (· ∈ M)] [DecidablePred (· ∈ map f M)]
    (hM : IsMoleculeIn P M) {xs : List P} (h : IsLayerOrder M xs) {s t : P}
    (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t) :
    (ℓ.comap ⟨f, isMap_of_isInclusion f⟩ hP).pathCell hM h hs ht =
      ℓ.pathCell ((isMoleculeIn_map_iff f M).2 hM) (h.map_of_isInclusion f)
        ((map_boundary f M 0 false).symm.trans ((congrArg (map f) hs).trans (map_Iic f s)))
        ((map_boundary f M 0 true).symm.trans ((congrArg (map f) ht).trans (map_Iic f t))) := by
  classical
  have hcol {a b : EdgeQuiver P} (q : Quiver.Path a b) :
      ∀ e ∈ pathEdges q, grade ℕ ((⟨f, isMap_of_isInclusion f⟩ : Map P Q) e) = 1 := fun e he =>
    ((isMorphism f).grade_eq e).trans (grade_of_mem_pathEdges q he)
  refine PathCell.ext rfl rfl (heq_of_eq ?_) (heq_of_eq ?_) ?_
  all_goals try exact (Map.mapPath_freePrefunctor_comp_lift_of_forall _ ℓ.toPrefunctor _
    (hcol _)).trans (congrArg ℓ.toPrefunctor.mapPath
      ((Map.mapPath_pathOf_of_isInclusion f _ (hM.boundary 1 _)
        ((krullDim_boundary_le _ 1 _).trans_eq Nat.cast_one) _ _).trans
          (pathOf_congr (map_boundary f M 1 _))))
  exact ((compositeAlong_comap_of_isInclusion f ℓ hM h hs ht).conj _ _ _ _).heq

end Labelling

section FreeImage

variable {P : OGP.{u}} {Q : OGP.{u'}} [Fintype P] [DecidableLE P] [Fintype Q]
  [DecidableLE Q] {B : Type u₁} [Bicategory.{w, v} B] {hP : P.IsRDC} {hQ : Q.IsRDC}

namespace Labelling

theorem comap_toPrefunctor_comp_lift {W : Type u₂} [Quiver.{v₂} W] (F : Prefunctor W B)
    (ℓ : Labelling (FreeBicategory W) Q hQ) (ℓ' : Labelling B Q hQ)
    (h : ℓ'.toPrefunctor = ℓ.toPrefunctor ⋙q (lift F).toPrefunctor) (g : Map P Q) :
    (ℓ'.comap g hP).toPrefunctor = (ℓ.comap g hP).toPrefunctor ⋙q (lift F).toPrefunctor := by
  obtain ⟨G', hG', c'⟩ := ℓ'
  dsimp only at h
  subst h
  exact Prefunctor.ext (fun _ => rfl) fun _ _ e => by
    simp only [Labelling.comap, Prefunctor.comp_map]
    exact lift_map_lift _ _ _
theorem pathCell_comap_of_comp_lift {W : Type u₂} [Quiver.{v₂} W] (F : Prefunctor W B)
    (ℓ : Labelling (FreeBicategory W) Q hQ) (ℓ' : Labelling B Q hQ)
    (h : ℓ'.toPrefunctor = ℓ.toPrefunctor ⋙q (lift F).toPrefunctor) (g : Map P Q)
    {M : LowerSet P} [DecidablePred (· ∈ M)] (hM : IsMoleculeIn P M) {xs : List P}
    (hxs : IsLayerOrder M xs) {s t : P} (hs : P.boundary M 0 false = .Iic s)
    (ht : P.boundary M 0 true = .Iic t)
    (hc : ∀ (j : ℕ) (hj : j < xs.length), grade ℕ (g xs[j]) ≠ 2)
    {a b : FreeBicategory W} {p q : Quiver.Path a b}
    {φ : pathComp (𝟭q (FreeBicategory W)) p ⟶ pathComp (𝟭q (FreeBicategory W)) q}
    (he : (ℓ.comap g hP).pathCell hM hxs hs ht = ⟨a, b, p, q, φ⟩) :
    ∃ ψ, IsStructural F (pathComp (𝟭q _) p) (pathComp (𝟭q _) q) ψ ∧
      (ℓ'.comap g hP).pathCell hM hxs hs ht =
        ⟨_, _, (lift F).toPrefunctor.mapPath p, (lift F).toPrefunctor.mapPath q, ψ⟩ := by
  obtain ⟨G', hG', c'⟩ := ℓ'
  dsimp only at h
  subst h
  obtain ⟨rfl, rfl, hp, hq, -⟩ := PathCell.mk.inj he
  obtain rfl := eq_of_heq hp
  obtain rfl := eq_of_heq hq
  have hS0 : IsStructural (ℓ.toPrefunctor ⋙q (lift F).toPrefunctor) _ _
      ((Labelling.comap g hP (⟨ℓ.toPrefunctor ⋙q (lift F).toPrefunctor, hG', c'⟩ :
        Labelling B Q hQ)).compositeAlong hM hxs hs ht) :=
    isStructural_compositeAlong (hQ := hQ) g ⟨ℓ.toPrefunctor ⋙q (lift F).toPrefunctor, hG', c'⟩
      hM hxs hs ht hc
  have hS := hS0.of_comp_lift
  have hpath {v w : P} (r : Quiver.Path (V := EdgeQuiver P) v w) :
      (Labelling.comap g hP (⟨ℓ.toPrefunctor ⋙q (lift F).toPrefunctor, hG', c'⟩ :
        Labelling B Q hQ)).toPrefunctor.mapPath r =
        (lift F).toPrefunctor.mapPath ((ℓ.comap g hP).toPrefunctor.mapPath r) := by
    induction r with
    | nil => rfl
    | cons r e ih =>
      rw [Prefunctor.mapPath_cons, Prefunctor.mapPath_cons, Prefunctor.mapPath_cons, ih]
      exact congrArg _ (lift_map_lift _ _ _)
  have e {v w : P} (r : Quiver.Path (V := EdgeQuiver P) v w) :
      pathComp (Labelling.comap g hP (⟨ℓ.toPrefunctor ⋙q (lift F).toPrefunctor, hG', c'⟩ :
        Labelling B Q hQ)).toPrefunctor r =
        pathComp (𝟭q B) ((lift F).toPrefunctor.mapPath ((ℓ.comap g hP).toPrefunctor.mapPath r)) :=
    (pathComp_mapPath _ r).symm.trans (congrArg (pathComp (𝟭q B)) (hpath r))
  have hψ := (IsStructural.eqToHom_comp (F := F) (e _).symm (hS.comp_eqToHom (e _))).congr
    ((pathComp_comp_lift _ _ _).symm.trans
      (pathComp_mapPath (ℓ.comap g hP).toPrefunctor _).symm)
    ((pathComp_comp_lift _ _ _).symm.trans
      (pathComp_mapPath (ℓ.comap g hP).toPrefunctor _).symm)
  refine ⟨_, hψ, PathCell.ext rfl rfl (heq_of_eq (hpath _))
      (heq_of_eq (hpath _)) ?_⟩
  refine (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans ?_)
  exact ((eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _))).symm
end Labelling

end FreeImage

end Atoms.Molecule.OGP

namespace Atoms.Molecule.OGP.Labelling

theorem ext_of_locallyDiscrete {D : Type*} [Category* D]
    {P : OGP} [Fintype P] [DecidableLE P] {hP : P.IsRDC}
    {ℓ ℓ' : Labelling (LocallyDiscrete D) P hP} (h : ℓ.toPrefunctor = ℓ'.toPrefunctor) :
    ℓ = ℓ' := by
  obtain ⟨F, hF, c⟩ := ℓ
  obtain ⟨F', hF', c'⟩ := ℓ'
  obtain rfl : F = F' := h
  exact Labelling.ext rfl fun x hx s t hs ht => heq_of_eq (Subsingleton.elim _ _)

theorem isCommutative_of_locallyDiscrete {D : Type*}
    [Category* D] {P : OGP} [Fintype P] [DecidableLE P] {hP : P.IsRDC}
    (ℓ : Labelling (LocallyDiscrete D) P hP) : ℓ.IsCommutative :=
  fun _ _ _ _ _ _ _ _ _ _ => Subsingleton.elim _ _

end Atoms.Molecule.OGP.Labelling

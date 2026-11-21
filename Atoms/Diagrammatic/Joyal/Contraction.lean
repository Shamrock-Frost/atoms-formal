import Atoms.Diagrammatic.DiagrammaticSet
import Atoms.ForMathlib.AlgebraicTopology.SimplexCategory.Augmented.ExtraDegeneracyExtension
import Atoms.Shape.Cone.Map

open CategoryTheory MonoidalCategory Opposite Simplicial Atoms.Shape

universe u

namespace Atoms.Diagrammatic

def augmentedCone (G : Atom) : AugmentedSimplexCategory ⥤ Atom where
  obj a := cone G (AugmentedSimplexCategory.card a)
  map f := coneHom G (AugmentedSimplexCategory.toOrderHom f)
  map_id a := by
    rw [AugmentedSimplexCategory.toOrderHom_id]
    exact coneHom_id G _
  map_comp f g := coneHom_toOrderHom_comp G f g

def augmentedConeMap {G G' : Atom} (f : G ⟶ G') : augmentedCone G ⟶ augmentedCone G' where
  app a := coneMap f (AugmentedSimplexCategory.card a)
  naturality _ _ g := coneHom_comp_coneMap f (AugmentedSimplexCategory.toOrderHom g)

def coneRestriction (G : Atom) : DiagSet.{u} ⥤ (AugmentedSimplexCategoryᵒᵖ ⥤ Type u) :=
  (Functor.whiskeringLeft _ _ _).obj (augmentedCone G).op

def coneRestrictionMap {G G' : Atom} (f : G ⟶ G') :
    coneRestriction.{u} G' ⟶ coneRestriction G :=
  (Functor.whiskeringLeft _ _ _).map (NatTrans.op (augmentedConeMap f))

noncomputable def outputVertexElem (B : Atom) : B.ogp :=
  (Molecule.OGP.exists_boundary_zero_eq_Iic
    (B.isAtom.1 : Molecule.OGP.IsMoleculeIn _ ⊤) true).choose

theorem boundary_univ_zero_true_eq_singleton (B : Atom) :
    (B.ogp.boundary ⊤ 0 true : Set B.ogp) = {outputVertexElem B} := by
  have h := (Molecule.OGP.exists_boundary_zero_eq_Iic
    (B.isAtom.1 : Molecule.OGP.IsMoleculeIn _ ⊤) true).choose_spec
  exact (congrArg SetLike.coe h.2).trans h.1.Iic_eq

theorem dim_outputVertexElem (B : Atom) : grade ℕ (outputVertexElem B) = 0 :=
  Nat.le_zero.1 (Molecule.OGP.grade_le_of_mem_boundary (U := ⊤) (α := true) (by
    change outputVertexElem B ∈ (B.ogp.boundary ⊤ 0 true : Set B.ogp)
    rw [boundary_univ_zero_true_eq_singleton]
    exact Set.mem_singleton _))

noncomputable def outputVertex (B : Atom) : atomPoint ⟶ B :=
  have : IsIso (toAtomPoint (Atom.ofClosure B (outputVertexElem B))) :=
    isIso_toAtomPoint_of_dimension_eq_zero (by
      rw [Atom.dimension_ofClosure]
      exact dim_outputVertexElem B)
  inv (toAtomPoint _) ≫ Atom.closureIncl B (outputVertexElem B)

def coreFiltration (m : ℕ) (X : DiagSet.{u}) : Subfunctor X where
  obj U := {x | ∃ (B : Atom) (r : ℕ) (f : U.unop ⟶ cone B r) (z : X.obj (op (cone B r))),
    B.dimension ≤ m ∧ X.map f.op z = x}
  map g x := by
    rintro ⟨B, r, f, z, hB, rfl⟩
    exact ⟨B, r, g.unop ≫ f, z, hB, by simp⟩

theorem coreFiltration_mono (X : DiagSet.{u}) {m m' : ℕ} (h : m ≤ m') :
    coreFiltration m X ≤ coreFiltration m' X := by
  rintro U x ⟨B, r, f, z, hB, rfl⟩
  exact ⟨B, r, f, z, hB.trans h, rfl⟩

structure CoherentContraction (B : Atom) (X : DiagSet.{u}) extends
    AugmentedSimplexCategory.ExtraDegeneracy ((coneRestriction B).obj X) where
  mem_coreFiltration (y : AugmentedSimplexCategoryᵒᵖ) (x : X.obj (op (cone B
      (AugmentedSimplexCategory.card y.unop)))) :
    x ∈ (coreFiltration (B.dimension - 1) X).obj
        (op (cone B (AugmentedSimplexCategory.card y.unop))) →
      h.app y x ∈ (coreFiltration (B.dimension - 1) X).obj
        (op (cone B (AugmentedSimplexCategory.card (WithInitial.of ⦋0⦌ ⊗ y.unop))))
  map_coneMap_outputVertex (x : X.obj (op B)) :
    X.map (coneMap (outputVertex B) 1).op (h.app (op WithInitial.star) x) =
      X.map (toAtomPoint (cone atomPoint 1)).op (X.map (outputVertex B).op x)

@[simp] theorem coneRestrictionMap_app_app {G G' : Atom} (f : G ⟶ G') (X : DiagSet.{u})
    (a : AugmentedSimplexCategoryᵒᵖ) :
    ((coneRestrictionMap f).app X).app a =
      X.map (coneMap f (AugmentedSimplexCategory.card a.unop)).op :=
  rfl

theorem coneRestrictionMap_comp {G G' G'' : Atom} (f : G ⟶ G') (g : G' ⟶ G'') :
    coneRestrictionMap.{u} (f ≫ g) = coneRestrictionMap g ≫ coneRestrictionMap f := by
  ext X a x
  simp only [coneRestrictionMap_app_app, NatTrans.comp_app, coneMap_comp, op_comp,
    Functor.map_comp]
  rfl

@[simp] theorem coneRestrictionMap_id (G : Atom) : coneRestrictionMap.{u} (𝟙 G) = 𝟙 _ := by
  ext X a x
  simp only [coneRestrictionMap_app_app, coneMap_id, op_id, X.map_id]
  rfl

@[simp] theorem outputVertex_apply (B : Atom) (d : atomPoint.ogp) :
    outputVertex B d = outputVertexElem B := by
  rw [outputVertex, ConcreteCategory.comp_apply]
  let W := Atom.ofClosure B (outputVertexElem B)
  have hW : W.dimension = 0 := by
    rw [Atom.dimension_ofClosure]
    exact dim_outputVertexElem B
  have htop : ∀ w : W.ogp, w = W.top := fun w =>
    GradeOrder.eq_of_le_of_grade_le (W.le_top w) (by rw [← W.dimension_eq, hW]; omega)
  exact (congrArg (Atom.closureIncl B (outputVertexElem B)) (htop _)).trans
    (Atom.closureIncl_top _ _)

theorem isInclusionHom_outputVertex (A : Atom) : IsInclusionHom (outputVertex A) :=
  fun _ _ _ => Subsingleton.elim _ _

theorem boundary_closure_top_zero_true (B : Atom) :
    (B.ogp.boundary (.Iic B.top) 0 true : Set B.ogp) = {outputVertexElem B} := by
  rw [B.Iic_top]
  exact boundary_univ_zero_true_eq_singleton B

theorem outputVertex_comp_of_isCollapseHom {U V : Atom} (q : U ⟶ V) (hq : IsCollapseHom q) :
    outputVertex U ≫ q = outputVertex V := by
  refine Atom.hom_ext fun d => ?_
  rw [ConcreteCategory.comp_apply, outputVertex_apply, outputVertex_apply]
  have htop : q U.top = V.top :=
    hq.apply_top
  have h := (Atom.isMap q).image_boundary U.top 0 true
  rw [htop, boundary_closure_top_zero_true, boundary_closure_top_zero_true,
    Set.image_singleton] at h
  exact Set.singleton_eq_singleton_iff.1 h

theorem outputVertex_cone_one (B : Atom) : outputVertex (cone B 1) = conePoint B 1 0 := by
  refine Atom.hom_ext fun d => ?_
  rw [outputVertex_apply, Subsingleton.elim d default]
  have h := boundary_closure_top_zero_true (cone B 1)
  rw [boundary_closure_top_zero_true_cone_one] at h
  exact (Set.singleton_eq_singleton_iff.1 h).symm

section ConeAlgebra

open AugmentedSimplexCategory

private structure ConeAlgebra (B : Atom) where
  ε : cone B 1 ⟶ B
  coneIncl_comp_ε : coneIncl B 1 ≫ ε = 𝟙 B
  coneMap_ε_comp_ε : coneMap ε 1 ≫ ε =
    (coneAssoc B 1 1).hom ≫ coneHom B (OrderHom.const _ (0 : Fin 1)) ≫ ε

@[reassoc] private lemma coneMap_comp_eqToHom {B B' : Atom} (f : B ⟶ B') {r s : ℕ} (h : r = s) :
    coneMap f r ≫ eqToHom (congrArg (cone B') h) = eqToHom (congrArg (cone B) h) ≫ coneMap f s := by
  subst h
  simp

@[reassoc] private lemma coneAssoc_inv_comp_eqToHom (B : Atom) (k : ℕ) {r s : ℕ} (h : r = s) :
    (coneAssoc B k r).inv ≫ eqToHom (congrArg (cone (cone B k)) h) =
      eqToHom (congrArg (cone B) (congrArg (k + ·) h)) ≫ (coneAssoc B k s).inv := by
  subst h
  simp

namespace ConeAlgebra

variable {B : Atom} (A : ConeAlgebra B)

private def κ (a : AugmentedSimplexCategory) : cone B (card (𝟘 ⊗ a)) ⟶ cone B (card a) :=
  eqToHom (congrArg (cone B) (card_zero_tensorObj a)) ≫ (coneAssoc B 1 (card a)).inv ≫
    coneMap A.ε (card a)

private def shiftHom {a' a : AugmentedSimplexCategory} (f : a' ⟶ a) :
    Fin (1 + card a') →o Fin (1 + card a) :=
  ⟨fun i => Fin.cast (card_zero_tensorObj a)
      (toFun (𝟘 ◁ f) (Fin.cast (card_zero_tensorObj a').symm i)),
    fun _ _ hij => Fin.le_iff_val_le_val.2 (Fin.le_iff_val_le_val.1
      (monotone_toFun _ (Fin.le_iff_val_le_val.2 (Fin.le_iff_val_le_val.1 hij))))⟩

private lemma shiftHom_castAdd {a' a : AugmentedSimplexCategory} (f : a' ⟶ a) (i : Fin 1) :
    shiftHom f (Fin.castAdd (card a') i) = Fin.castAdd (card a) i :=
  Fin.ext ((val_toFun_whiskerLeft_of_eq_zero _ _ (Fin.val_eq_zero i)).trans
    (Fin.val_eq_zero i).symm)

private lemma shiftHom_natAdd {a' a : AugmentedSimplexCategory} (f : a' ⟶ a) (j : Fin (card a')) :
    shiftHom f (Fin.natAdd 1 j) = Fin.natAdd 1 (toOrderHom f j) := by
  have hne : (Fin.cast (card_zero_tensorObj a').symm (Fin.natAdd 1 j)).val ≠ 0 := by
    simp only [Fin.val_cast, Fin.val_natAdd]
    omega
  refine Fin.ext ((val_toFun_whiskerLeft_of_ne_zero _ _ hne).trans ?_)
  have hj : ∀ k : Fin (card a'), k = j →
      (toFun f k).val + 1 = (Fin.natAdd 1 (toOrderHom f j)).val := by
    rintro k rfl
    rw [Fin.val_natAdd, Nat.add_comm]
    rfl
  exact hj _ (Fin.ext (by simp))

private lemma κ_comp_coneHom {a' a : AugmentedSimplexCategory} (f : a' ⟶ a) :
    A.κ a' ≫ coneHom B (toOrderHom f) = coneHom B (toOrderHom (𝟘 ◁ f)) ≫ A.κ a := by
  have key := coneHom_comp_coneAssoc B 1 (toOrderHom f) (shiftHom f) (shiftHom_castAdd f)
    (shiftHom_natAdd f)
  have key' : (coneAssoc B 1 (card a')).inv ≫ coneHom (cone B 1) (toOrderHom f) =
      coneHom B (shiftHom f) ≫ (coneAssoc B 1 (card a)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← key, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  dsimp only [κ]
  simp only [Category.assoc]
  rw [← coneHom_comp_coneMap, reassoc_of% key', eqToHom_cone B (card_zero_tensorObj a'),
    eqToHom_cone B (card_zero_tensorObj a), coneHom_comp_assoc, coneHom_comp_assoc]
  rfl

private lemma coneHom_inr_comp_κ (a : AugmentedSimplexCategory) :
    coneHom B (toOrderHom (inr 𝟘 a)) ≫ A.κ a = 𝟙 _ := by
  dsimp only [κ]
  rw [eqToHom_cone B (card_zero_tensorObj a), coneHom_comp_assoc]
  have h : (OrderHom.comp ⟨Fin.cast (card_zero_tensorObj a), fun _ _ hij => hij⟩
      (toOrderHom (inr 𝟘 a))) =
      ⟨Fin.natAdd 1, fun _ _ hij => Fin.natAdd_le_natAdd_iff 1 |>.2 hij⟩ :=
    OrderHom.ext _ _ (funext fun i => Fin.ext (val_toFun_inr 𝟘 a i))
  rw [h, ← coneMap_coneIncl_comp_coneAssoc, Category.assoc, Iso.hom_inv_id_assoc,
    ← coneMap_comp, A.coneIncl_comp_ε, coneMap_id]

private def mergeHom (n : ℕ) : Fin (1 + 1 + n) →o Fin (1 + n) :=
  ⟨fun i => ⟨i.val - 1, by omega⟩, fun _ _ hij => Fin.mk_le_mk.2
    (Nat.sub_le_sub_right (Fin.le_iff_val_le_val.1 hij) 1)⟩

private lemma val_mergeHom (n : ℕ) (i : Fin (1 + 1 + n)) : (mergeHom n i).val = i.val - 1 :=
  rfl

private lemma coneHom_mu_comp_κ (a : AugmentedSimplexCategory) :
    coneHom B (toOrderHom ((α_ 𝟘 𝟘 a).inv ≫ zeroMul ▷ a)) ≫ A.κ a = A.κ (𝟘 ⊗ a) ≫ A.κ a := by
  have hc := coneAssoc_hom_comp_coneAssoc_hom B 1 1 (card a)
  have hZ : coneMap (coneAssoc B 1 1).hom (card a) =
      (coneAssoc (cone B 1) 1 (card a)).hom ≫ (coneAssoc B 1 (1 + card a)).hom ≫
        eqToHom (congrArg (cone B) (Nat.add_assoc 1 1 (card a)).symm) ≫
          (coneAssoc B (1 + 1) (card a)).inv := by
    rw [← Category.assoc, hc, Category.assoc, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Iso.hom_inv_id, Category.comp_id]
  have hc' : (coneAssoc B 1 (1 + card a)).inv ≫ (coneAssoc (cone B 1) 1 (card a)).inv ≫
      coneMap (coneAssoc B 1 1).hom (card a) =
        eqToHom (congrArg (cone B) (Nat.add_assoc 1 1 (card a)).symm) ≫
          (coneAssoc B (1 + 1) (card a)).inv := by
    rw [hZ, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
  have hm := coneMap_coneMap_comp_coneAssoc A.ε 1 (card a)
  have hm' : coneMap A.ε (1 + card a) ≫ (coneAssoc B 1 (card a)).inv =
      (coneAssoc (cone B 1) 1 (card a)).inv ≫ coneMap (coneMap A.ε 1) (card a) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hm, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hh := coneMap_coneHom_comp_coneAssoc B (OrderHom.const _ (0 : Fin 1)) (card a)
    (mergeHom (card a))
    (fun i => Fin.ext (by
      rw [val_mergeHom, Fin.val_castAdd, Fin.val_castAdd, Fin.val_eq_zero]
      have := i.isLt
      omega))
    (fun j => Fin.ext (by rw [val_mergeHom, Fin.val_natAdd, Fin.val_natAdd]; omega))
  have hh' : (coneAssoc B (1 + 1) (card a)).inv ≫
      coneMap (coneHom B (OrderHom.const _ (0 : Fin 1))) (card a) =
        coneHom B (mergeHom (card a)) ≫ (coneAssoc B 1 (card a)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hh, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  dsimp only [κ]
  simp only [Category.assoc]
  rw [coneMap_comp_eqToHom_assoc, coneAssoc_inv_comp_eqToHom_assoc, eqToHom_trans_assoc,
    reassoc_of% hm', ← coneMap_comp, A.coneMap_ε_comp_ε, coneMap_comp, coneMap_comp,
    reassoc_of% hc', reassoc_of% hh', eqToHom_trans_assoc, eqToHom_cone B (card_zero_tensorObj a),
    coneHom_comp_assoc, eqToHom_cone, coneHom_comp_assoc]
  · congr 2
    refine OrderHom.ext _ _ (funext fun i => ?_)
    apply Fin.ext
    exact val_toFun_associator_inv_comp_whiskerRight_zeroMul a i
  all_goals
    simp only [card_zero_tensorObj]
    try omega

private lemma κ_comp_coneMap {B' : Atom} (A' : ConeAlgebra B') (f : B ⟶ B')
    (hf : coneMap f 1 ≫ A'.ε = A.ε ≫ f) (a : AugmentedSimplexCategory) :
    A.κ a ≫ coneMap f (card a) = coneMap f (card (𝟘 ⊗ a)) ≫ A'.κ a := by
  have hm := coneMap_coneMap_comp_coneAssoc f 1 (card a)
  have hm' : coneMap f (1 + card a) ≫ (coneAssoc B' 1 (card a)).inv =
      (coneAssoc B 1 (card a)).inv ≫ coneMap (coneMap f 1) (card a) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hm, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  dsimp only [κ]
  simp only [Category.assoc]
  rw [← coneMap_comp, ← hf, coneMap_comp, coneMap_comp_eqToHom_assoc f (card_zero_tensorObj a),
    reassoc_of% hm']

private def extraDegeneracy (X : DiagSet.{u}) : ExtraDegeneracy ((coneRestriction B).obj X) where
  h :=
    { app a := X.map (A.κ a.unop).op
      naturality a a' g := by
        have := congrArg (fun f => X.map f.op) (A.κ_comp_coneHom g.unop)
        simp only [op_comp, X.map_comp] at this
        exact this }
  h_comp_counit := by
    ext a : 2
    have := congrArg (fun f => X.map f.op) (A.coneHom_inr_comp_κ a.unop)
    simp only [op_comp, X.map_comp, op_id, X.map_id] at this
    exact this
  h_comp_comult := by
    ext a : 2
    have := congrArg (fun f => X.map f.op) (A.coneHom_mu_comp_κ a.unop)
    simp only [op_comp, X.map_comp] at this
    exact this

private lemma coneRestrictionMap_comp_extraDegeneracy {B' : Atom} (A' : ConeAlgebra B')
    (f : B ⟶ B') (hf : coneMap f 1 ≫ A'.ε = A.ε ≫ f) (X : DiagSet.{u}) :
    (coneRestrictionMap f).app X ≫ (A.extraDegeneracy X).h =
      (A'.extraDegeneracy X).h ≫ (decalage _).map ((coneRestrictionMap f).app X) := by
  ext a : 2
  have := congrArg (fun f => X.map f.op) (A.κ_comp_coneMap A' f hf a.unop)
  simp only [op_comp, X.map_comp] at this
  exact this

end ConeAlgebra

private def pointAlgebra : ConeAlgebra atomPoint where
  ε := toAtomPoint _
  coneIncl_comp_ε := Subsingleton.elim _ _
  coneMap_ε_comp_ε := Subsingleton.elim _ _

private def coneOneAlgebra (B : Atom) : ConeAlgebra (cone B 1) where
  ε := (coneAssoc B 1 1).hom ≫ coneHom B (OrderHom.const _ (0 : Fin 1))
  coneIncl_comp_ε := coneIncl_comp_coneAssoc_comp_coneHom B
  coneMap_ε_comp_ε := coneMap_coneAssoc_comp_coneHom_comp B

private def pointDeg (X : DiagSet.{u}) : ExtraDegeneracy ((coneRestriction atomPoint).obj X) :=
  pointAlgebra.extraDegeneracy X

private def coneOneDeg (X : DiagSet.{u}) (B : Atom) :
    ExtraDegeneracy ((coneRestriction (cone B 1)).obj X) :=
  (coneOneAlgebra B).extraDegeneracy X

private lemma outputVertex_atomPoint : outputVertex atomPoint = 𝟙 atomPoint :=
  Subsingleton.elim _ _

private lemma pointDeg_over (X : DiagSet.{u}) :
    (pointDeg X).h ≫ (decalage _).map ((coneRestrictionMap (outputVertex atomPoint)).app X) =
      (coneRestrictionMap (outputVertex atomPoint)).app X ≫ (pointDeg X).h := by
  rw [outputVertex_atomPoint, coneRestrictionMap_id, NatTrans.id_app]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

private lemma coneOneDeg_over (X : DiagSet.{u}) (B : Atom) :
    (coneOneDeg X B).h ≫ (decalage _).map ((coneRestrictionMap (outputVertex (cone B 1))).app X) =
      (coneRestrictionMap (outputVertex (cone B 1))).app X ≫ (pointDeg X).h := by
  refine (pointAlgebra.coneRestrictionMap_comp_extraDegeneracy (coneOneAlgebra B)
    (outputVertex (cone B 1)) ?_ X).symm
  rw [outputVertex_cone_one]
  refine cone_hom_ext (B := atomPoint) (r := 1) (F := B) (s := 1) (fun _ => 0)
    (fun i => by simp [coneOneAlgebra]) (fun i => ?_) ?_
  · rw [← Category.assoc, Subsingleton.elim (conePoint atomPoint 1 i ≫ pointAlgebra.ε) (𝟙 _),
      Category.id_comp]
  · simp only [coneOneAlgebra, pointAlgebra]
    rw [coneIncl_comp_coneMap_assoc, coneIncl_comp_coneAssoc_comp_coneHom, Category.comp_id,
      ← Category.assoc, Subsingleton.elim (coneIncl atomPoint 1 ≫ toAtomPoint _) (𝟙 _),
      Category.id_comp]

private lemma coneOneDeg_compat (X : DiagSet.{u}) {B B' : Atom} (q : cone B 1 ⟶ cone B' 1)
    (hq : IsCollapseHom q) :
    (coneRestrictionMap q).app X ≫ (coneOneDeg X B).h =
      (coneOneDeg X B').h ≫ (decalage _).map ((coneRestrictionMap q).app X) :=
  (coneOneAlgebra B).coneRestrictionMap_comp_extraDegeneracy (coneOneAlgebra B') q
    (coneMap_comp_coneAssoc_comp_coneHom_of_isCollapseHom q hq) X

private lemma coneOneDeg_compat_atomPoint (X : DiagSet.{u}) {B : Atom} (q : cone B 1 ⟶ atomPoint) :
    (coneRestrictionMap q).app X ≫ (coneOneDeg X B).h =
      (pointDeg X).h ≫ (decalage _).map ((coneRestrictionMap q).app X) :=
  (coneOneAlgebra B).coneRestrictionMap_comp_extraDegeneracy pointAlgebra q
    (Subsingleton.elim _ _) X

end ConeAlgebra

noncomputable def isoRep (B : Atom) : Atom :=
  Quotient.out (⟦B⟧ : Quotient (isIsomorphicSetoid Atom))

theorem nonempty_iso_isoRep (B : Atom) : Nonempty (isoRep B ≅ B) :=
  Quotient.mk_out (s := isIsomorphicSetoid Atom) B

theorem isoRep_eq_of_iso {B B' : Atom} (e : B ≅ B') : isoRep B = isoRep B' :=
  congrArg Quotient.out (Quotient.sound ⟨e⟩)

theorem eq_of_iso_of_isoRep_eq {B B' : Atom} (hB : isoRep B = B) (hB' : isoRep B' = B')
    (e : B ≅ B') : B = B' := by
  rw [← hB, ← hB', isoRep_eq_of_iso e]

theorem isoRep_isoRep (B : Atom) : isoRep (isoRep B) = isoRep B :=
  isoRep_eq_of_iso (nonempty_iso_isoRep B).some

private def IsRep (C : Atom) : Prop :=
  C = atomPoint ∨ (IsCore C ∧ 0 < C.dimension ∧ isoRep C = C)

private lemma IsRep.isCore {C : Atom} (hC : IsRep C) : IsCore C := by
  rcases hC with rfl | ⟨h, -, -⟩
  · exact (isCore_iff_dimension_eq_zero (by rw [dimension_atomPoint]; omega)).2
      dimension_atomPoint
  · exact h

private lemma IsRep.eq_of_iso {C C' : Atom} (hC : IsRep C) (hC' : IsRep C') (e : C ≅ C') :
    C = C' := by
  have hd := Atom.dimension_eq_of_iso e
  rcases hC with rfl | ⟨-, h0, hr⟩ <;> rcases hC' with rfl | ⟨-, h0', hr'⟩
  · rfl
  · rw [dimension_atomPoint] at hd
    omega
  · rw [dimension_atomPoint] at hd
    omega
  · rw [← hr, ← hr', isoRep_eq_of_iso e]

private lemma IsRep.isCore_pos_or {C : Atom} (hC : IsRep C) :
    (IsCore C ∧ 0 < C.dimension) ∨ C = atomPoint := by
  rcases hC with rfl | ⟨h, h0, -⟩
  · exact Or.inr rfl
  · exact Or.inl ⟨h, h0⟩

private lemma exists_isRep_iso_cone (U : Atom) :
    ∃ (C : Atom) (r : ℕ), IsRep C ∧ Nonempty (U ≅ cone C r) := by
  obtain ⟨B, r, hB, ⟨e⟩⟩ := exists_isCore_iso_cone U
  by_cases h0 : B.dimension = 0
  · have := isIso_toAtomPoint_of_dimension_eq_zero h0
    exact ⟨atomPoint, r, Or.inl rfl, ⟨e ≪≫ (coneFunctor r).mapIso (asIso (toAtomPoint B))⟩⟩
  · obtain ⟨e'⟩ := nonempty_iso_isoRep B
    refine ⟨isoRep B, r, Or.inr ⟨IsCore.of_iso hB e'.symm, ?_, isoRep_eq_of_iso e'⟩,
      ⟨e ≪≫ (coneFunctor r).mapIso e'.symm⟩⟩
    rw [Atom.dimension_eq_of_iso e']
    omega

open AugmentedSimplexCategory

private def coneDeg (X : DiagSet.{u}) {m : ℕ}
    (deg : ∀ C : Atom, IsRep C → C.dimension < m →
      ExtraDegeneracy ((coneRestriction C).obj X))
    (C : Atom) (hC : IsRep C) (hm : C.dimension < m) :
    (K : ℕ) → ExtraDegeneracy ((coneRestriction (cone C K)).obj X)
  | 0 => deg C hC hm
  | K + 1 => coneOneDeg X (cone C K)

private structure Family (X : DiagSet.{u}) (m : ℕ) where
  deg : ∀ C : Atom, IsRep C → C.dimension < m →
    ExtraDegeneracy ((coneRestriction C).obj X)
  deg_atomPoint : ∀ (hC : IsRep atomPoint) (hm : atomPoint.dimension < m),
    deg atomPoint hC hm = pointDeg X
  over : ∀ (C : Atom) (hC : IsRep C) (hm : C.dimension < m),
    (deg C hC hm).h ≫ (decalage _).map ((coneRestrictionMap (outputVertex C)).app X) =
      (coneRestrictionMap (outputVertex C)).app X ≫ (pointDeg X).h
  compat : ∀ (C : Atom) (hC : IsRep C) (hm : C.dimension < m) (C' : Atom) (hC' : IsRep C')
    (hm' : C'.dimension < m) (K : ℕ) (q : C ⟶ cone C' K), IsCollapseHom q → ¬ IsIso q →
      (coneRestrictionMap q).app X ≫ (deg C hC hm).h =
        (coneDeg X deg C' hC' hm' K).h ≫ (decalage _).map ((coneRestrictionMap q).app X)

namespace Family

variable {X : DiagSet.{u}} {m : ℕ} (F : Family X m)

private lemma coneDeg_over (C : Atom) (hC : IsRep C) (hm : C.dimension < m) (K : ℕ) :
    (coneDeg X F.deg C hC hm K).h ≫
        (decalage _).map ((coneRestrictionMap (outputVertex (cone C K))).app X) =
      (coneRestrictionMap (outputVertex (cone C K))).app X ≫ (pointDeg X).h := by
  cases K with
  | zero => exact F.over C hC hm
  | succ K => exact coneOneDeg_over X (cone C K)

private lemma coneDeg_compat {C C' : Atom} (hC : IsRep C) (hm : C.dimension < m)
    (hC' : IsRep C') (hm' : C'.dimension < m) (K K' : ℕ) (q : cone C K ⟶ cone C' K')
    (hq : IsCollapseHom q) :
    (coneRestrictionMap q).app X ≫ (coneDeg X F.deg C hC hm K).h =
      (coneDeg X F.deg C' hC' hm' K').h ≫ (decalage _).map ((coneRestrictionMap q).app X) := by
  cases K with
  | zero =>
    by_cases hiso : IsIso q
    · obtain ⟨rfl, ⟨e⟩⟩ := eq_and_nonempty_iso_of_iso_cone hC.isCore hC'.isCore (asIso q)
      obtain rfl := hC.eq_of_iso hC' e
      obtain rfl : q = 𝟙 _ := congrArg Iso.hom (Atom.iso_eq (asIso q) (Iso.refl _))
      rw [coneRestrictionMap_id, NatTrans.id_app]
      simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
    · exact F.compat C hC hm C' hC' hm' K' q hq hiso
  | succ K =>
    cases K' with
    | zero =>
      rcases hC'.isCore_pos_or with ⟨hcore, h0⟩ | rfl
      · exact absurd (pos_of_isCollapseHom hcore h0 (Nat.succ_pos K) q hq) (lt_irrefl 0)
      · have := coneOneDeg_compat_atomPoint X q
        rw [← F.deg_atomPoint hC' hm'] at this
        exact this
    | succ K' => exact coneOneDeg_compat X q hq

end Family

private def lowerCells (X : DiagSet.{u}) (G : Atom) (m : ℕ) :
    Subfunctor ((coneRestriction G).obj X) where
  obj a := (coreFiltration m X).obj (op (cone G (card a.unop)))
  map f := (coreFiltration m X).map ((augmentedCone G).map f.unop).op

private structure Pres (m : ℕ) (G : Atom) where
  C : Atom
  hC : IsRep C
  hm : C.dimension < m
  K : ℕ
  q : G ⟶ cone C K
  hq : IsCollapseHom q

private lemma coneRestrictionMap_mem_lowerCells (X : DiagSet.{u}) {m : ℕ} {G C : Atom}
    (hm : C.dimension < m + 1) {K : ℕ} (q : G ⟶ cone C K) (a : AugmentedSimplexCategoryᵒᵖ)
    (y : X.obj (op (cone (cone C K) (card a.unop)))) :
    ((coneRestrictionMap q).app X).app a y ∈ (lowerCells X G m).obj a :=
  ⟨C, K + card a.unop, coneMap q (card a.unop) ≫ (coneAssoc C K (card a.unop)).hom,
    X.map (coneAssoc C K (card a.unop)).inv.op y, by omega,
    (by rw [← X.map_comp_apply, ← op_comp, Category.assoc, Iso.hom_inv_id,
        Category.comp_id] : X.map (coneMap q (card a.unop) ≫ (coneAssoc C K (card a.unop)).hom).op
          (X.map (coneAssoc C K (card a.unop)).inv.op y) = X.map (coneMap q (card a.unop)).op y)⟩

private def Pres.π (X : DiagSet.{u}) {m : ℕ} {G : Atom} (i : Pres (m + 1) G) :
    (coneRestriction (cone i.C i.K)).obj X ⟶ (lowerCells X G m).toFunctor :=
  Subfunctor.lift ((coneRestrictionMap i.q).app X) (by
    rintro a _ ⟨y, rfl⟩
    exact coneRestrictionMap_mem_lowerCells X i.hm i.q a y)

private lemma isNondegenerate_map_inv {X : DiagSet.{u}} {b b' : Atom} (e : b ≅ b')
    {w : X.obj (op b)} (hw : Homotopical.EZCategory.IsNondegenerate X w) :
    Homotopical.EZCategory.IsNondegenerate X (X.map e.inv.op w) := by
  intro c p hp ⟨z, hz⟩
  have : IsIso (e.hom ≫ p) := hw (e.hom ≫ p) inferInstance ⟨z, by
    rw [op_comp, X.map_comp_apply, hz, ← X.map_comp_apply, ← op_comp, Iso.hom_inv_id, op_id,
      X.map_id_apply]⟩
  exact IsIso.of_isIso_comp_left e.hom p

private lemma card_coneCoord_apply_top {G C : Atom} {K r : ℕ} (Q : G ⟶ cone C K)
    (hQ : IsCollapseHom Q) (hK : K ≤ r) :
    (coneCoord C r ((Q ≫ coneHom C (Fin.castLEOrderEmb hK).toOrderHom) G.top)).2.card = K := by
  have htop : Q G.top = (cone C K).top :=
    hQ.apply_top
  rw [ConcreteCategory.comp_apply, htop, ← WithBot.map_coe, coneCoord_coneHom, coneCoord_top]
  dsimp only
  exact (Finset.card_image_of_injective Finset.univ (f := ⇑(Fin.castLEOrderEmb hK).toOrderHom)
    (fun _ _ h => (Fin.castLEOrderEmb hK).injective h)).trans (by simp)

private structure RootForm (X : DiagSet.{u}) (m : ℕ) (G : Atom) (n : ℕ) (c : X.obj (op (cone G n)))
    where
  C : Atom
  hC : IsRep C
  hm : C.dimension < m
  K : ℕ
  r : ℕ
  hK : K ≤ r
  Q : G ⟶ cone C K
  hQ : IsCollapseHom Q
  ℓ : cone (cone C K) n ⟶ cone C r
  hℓ : coneIncl (cone C K) n ≫ ℓ = coneHom C (Fin.castLEOrderEmb hK).toOrderHom
  w : X.obj (op (cone C r))
  hw : Homotopical.EZCategory.IsNondegenerate X w
  hρ : IsCollapseHom (coneMap Q n ≫ ℓ)
  hc : X.map (coneMap Q n ≫ ℓ).op w = c

private lemma RootForm.value_eq {X : DiagSet.{u}} {m : ℕ} (F : Family X m) {G : Atom}
    {a : AugmentedSimplexCategory} {c c' : X.obj (op (cone G (card a)))}
    (R : RootForm X m G (card a) c) (R' : RootForm X m G (card a) c') (hcc : c = c') :
    ((coneDeg X F.deg R.C R.hC R.hm R.K).h ≫
        (decalage _).map ((coneRestrictionMap R.Q).app X)).app (op a) (X.map R.ℓ.op R.w) =
      ((coneDeg X F.deg R'.C R'.hC R'.hm R'.K).h ≫
        (decalage _).map ((coneRestrictionMap R'.Q).app X)).app (op a) (X.map R'.ℓ.op R'.w) := by
  obtain ⟨C, hC, hm, K, r, hK, Q, hQ, ℓ, hℓ, w, hw, hρ, hc⟩ := R
  obtain ⟨C', hC', hm', K', r', hK', Q', hQ', ℓ', hℓ', w', hw', hρ', hc'⟩ := R'
  subst hcc
  dsimp only
  have := isSplitEpi_of_isCollapseHom _ hρ
  have := isSplitEpi_of_isCollapseHom _ hρ'
  obtain ⟨e, ⟨he, hew⟩, -⟩ := Homotopical.EZCategory.existsUnique_iso_of_isNondegenerate X
    (coneMap Q (card a) ≫ ℓ) (coneMap Q' (card a) ≫ ℓ') w w' inferInstance hw inferInstance hw'
    (hc.trans hc'.symm)
  obtain ⟨rfl, ⟨eC⟩⟩ := eq_and_nonempty_iso_of_iso_cone hC.isCore hC'.isCore e
  obtain rfl := hC.eq_of_iso hC' eC
  obtain rfl : e = Iso.refl _ := Atom.iso_eq _ _
  simp only [Iso.refl_hom, Category.comp_id, op_id, X.map_id_apply] at he hew
  subst hew
  have hQℓ : ∀ {K₀ : ℕ} (hK₀ : K₀ ≤ r) (Q₀ : G ⟶ cone C K₀)
      (ℓ₀ : cone (cone C K₀) (card a) ⟶ cone C r),
      coneIncl (cone C K₀) (card a) ≫ ℓ₀ = coneHom C (Fin.castLEOrderEmb hK₀).toOrderHom →
        coneIncl G (card a) ≫ coneMap Q₀ (card a) ≫ ℓ₀ =
          Q₀ ≫ coneHom C (Fin.castLEOrderEmb hK₀).toOrderHom := fun hK₀ Q₀ ℓ₀ h => by
    rw [coneIncl_comp_coneMap_assoc, h]
  obtain rfl : K = K' := by
    rw [← card_coneCoord_apply_top Q hQ hK, ← card_coneCoord_apply_top Q' hQ' hK',
      ← hQℓ hK Q ℓ hℓ, ← hQℓ hK' Q' ℓ' hℓ', he]
  obtain rfl : Q = Q' := by
    have := mono_of_isInclusionHom _ (isInclusionHom_coneHom C
      (σ := (Fin.castLEOrderEmb hK).toOrderHom) (fun _ _ h => (Fin.castLEOrderEmb hK).injective h))
    rw [← cancel_mono (coneHom C (Fin.castLEOrderEmb hK).toOrderHom), ← hQℓ hK Q ℓ hℓ,
      ← hQℓ hK Q' ℓ' hℓ', he]
  have := isSplitEpi_of_isCollapseHom _ (isCollapseHom_coneMap Q hQ (card a))
  obtain rfl : ℓ = ℓ' := (cancel_epi (coneMap Q (card a))).1 he
  rfl

private lemma Pres.exists_rootForm {X : DiagSet.{u}} {m : ℕ} (F : Family X m) {G : Atom}
    (i : Pres m G) (a : AugmentedSimplexCategory)
    (y : X.obj (op (cone (cone i.C i.K) (card a)))) :
    ∃ R : RootForm X m G (card a) (X.map (coneMap i.q (card a)).op y),
      ((coneDeg X F.deg R.C R.hC R.hm R.K).h ≫
          (decalage _).map ((coneRestrictionMap R.Q).app X)).app (op a) (X.map R.ℓ.op R.w) =
        ((coneDeg X F.deg i.C i.hC i.hm i.K).h ≫
          (decalage _).map ((coneRestrictionMap i.q).app X)).app (op a) y := by
  obtain ⟨b, ρy, wy, hρy, hwy, hy⟩ := Homotopical.EZCategory.exists_isNondegenerate X _ y
  obtain ⟨C', r', hC', ⟨e⟩⟩ := exists_isRep_iso_cone b
  have hρ : IsCollapseHom (ρy ≫ e.hom) :=
    collapses.comp_mem _ _ (@isCollapseHom_of_isSplitEpi _ _ ρy hρy) (isCollapseHom_of_iso e)
  have hyw : X.map (ρy ≫ e.hom).op (X.map e.inv.op wy) = y := by
    rw [← X.map_comp_apply, ← op_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id, hy]
  have hm' : C'.dimension < m := lt_of_le_of_lt (dimension_le_of_isCollapseHom_cone hC'.isCore
    ((coneAssoc i.C i.K (card a)).inv ≫ ρy ≫ e.hom)
    (collapses.comp_mem _ _ (isCollapseHom_of_iso (coneAssoc i.C i.K (card a)).symm) hρ)) i.hm
  obtain ⟨K'', hK'', q'', ℓ, hq'', hℓ, hρeq⟩ := exists_coneMap_comp_eq hC'.isCore_pos_or _ hρ
  refine ⟨⟨C', hC', hm', K'', r', hK'', i.q ≫ q'', collapses.comp_mem _ _ i.hq hq'', ℓ, hℓ,
    X.map e.inv.op wy, isNondegenerate_map_inv e hwy, ?_, ?_⟩, ?_⟩
  · rw [coneMap_comp, Category.assoc, hρeq]
    exact collapses.comp_mem _ _ (isCollapseHom_coneMap _ i.hq _) hρ
  · rw [coneMap_comp, Category.assoc, hρeq, op_comp, X.map_comp_apply, hyw]
  · dsimp only
    have hy' : X.map (coneMap q'' (card a)).op (X.map ℓ.op (X.map e.inv.op wy)) = y := by
      rw [← X.map_comp_apply, ← op_comp, hρeq, hyw]
    have key : (coneRestrictionMap q'').app X ≫ (coneDeg X F.deg i.C i.hC i.hm i.K).h ≫
        (decalage _).map ((coneRestrictionMap i.q).app X) =
          (coneDeg X F.deg C' hC' hm' K'').h ≫
            (decalage _).map ((coneRestrictionMap (i.q ≫ q'')).app X) := by
      rw [reassoc_of% (F.coneDeg_compat i.hC i.hm hC' hm' i.K K'' q'' hq''), ← Functor.map_comp,
        coneRestrictionMap_comp, NatTrans.comp_app]
    have := ConcreteCategory.congr_hom (NatTrans.congr_app key (op a))
      (X.map ℓ.op (X.map e.inv.op wy))
    subst hy'
    exact this.symm

private lemma Pres.exists_eq {X : DiagSet.{u}} {G : Atom} {m : ℕ} (n : ℕ)
    (x : X.obj (op (cone G n))) (hx : x ∈ (coreFiltration m X).obj (op (cone G n))) :
    ∃ (i : Pres (m + 1) G) (y : X.obj (op (cone (cone i.C i.K) n))),
      X.map (coneMap i.q n).op y = x := by
  obtain ⟨B', r, f, z, hB', rfl⟩ := hx
  obtain ⟨W, p, ι, hp, hι, rfl⟩ := exists_collapse_inclusion_factorization f
  obtain ⟨C, r', hC, ⟨e⟩⟩ := exists_isRep_iso_cone W
  obtain ⟨B'', s, hB'', ⟨e'⟩⟩ := exists_isCore_iso_cone B'
  have := mono_of_isInclusionHom ι hι
  have : IsIso (coneMap e'.hom r) := (inferInstance : IsIso ((coneFunctor r).map e'.hom))
  have hdim : C.dimension ≤ B''.dimension :=
    dimension_le_of_isInclusionHom_cone hC.isCore
      (e.inv ≫ ι ≫ coneMap e'.hom r ≫ (coneAssoc B'' s r).hom) (isInclusionHom_of_mono _)
  have hB'' : B''.dimension ≤ B'.dimension := by
    rw [Atom.dimension_eq_of_iso e', dimension_cone]
    omega
  obtain ⟨K, hK, Q, ℓ, hQ, -, hρ⟩ := exists_coneMap_comp_eq hC.isCore_pos_or (p ≫ e.hom)
    (collapses.comp_mem _ _ hp (isCollapseHom_of_iso e))
  refine ⟨⟨C, hC, by omega, K, Q, hQ⟩, X.map ℓ.op (X.map (e.inv ≫ ι).op z), ?_⟩
  dsimp only
  rw [← X.map_comp_apply, ← op_comp, ← X.map_comp_apply, ← op_comp, hρ, Category.assoc,
    Iso.hom_inv_id_assoc]

private lemma exists_extraDegeneracy_step (X : DiagSet.{u})
    (hX : ∀ G : Atom, IsCore G → ∀ a,
      HasLiftingProperty (boundary a).ι ((coneRestrictionMap (outputVertex G)).app X))
    {G : Atom} (hG : IsCore G) {m : ℕ} (F : Family X (m + 1)) :
    ∃ h : ExtraDegeneracy ((coneRestriction G).obj X),
      (h.h ≫ (decalage _).map ((coneRestrictionMap (outputVertex G)).app X) =
        (coneRestrictionMap (outputVertex G)).app X ≫ (pointDeg X).h) ∧
      (∀ (a : AugmentedSimplexCategoryᵒᵖ) (x : ((coneRestriction G).obj X).obj a),
        x ∈ (lowerCells X G m).obj a → h.h.app a x ∈ (lowerCells X G m).obj (op (𝟘 ⊗ a.unop))) ∧
      ∀ (C : Atom) (hC : IsRep C) (hm : C.dimension < m + 1) (K : ℕ) (q : G ⟶ cone C K),
        IsCollapseHom q → (coneRestrictionMap q).app X ≫ h.h =
          (coneDeg X F.deg C hC hm K).h ≫ (decalage _).map ((coneRestrictionMap q).app X) := by
  let P' := lowerCells X G m
  let hE := fun i : Pres (m + 1) G => coneDeg X F.deg i.C i.hC i.hm i.K
  have hsurj : ∀ (a : AugmentedSimplexCategoryᵒᵖ) (x : P'.toFunctor.obj a),
      ∃ (i : Pres (m + 1) G) (y : ((coneRestriction (cone i.C i.K)).obj X).obj a),
        (Pres.π X i).app a y = x := fun a x => by
    obtain ⟨i, y, hy⟩ := Pres.exists_eq (card a.unop) x.1 x.2
    exact ⟨i, y, Subtype.ext hy⟩
  have hwd : ∀ (a : AugmentedSimplexCategoryᵒᵖ) (i j : Pres (m + 1) G)
      (y : ((coneRestriction (cone i.C i.K)).obj X).obj a)
      (y' : ((coneRestriction (cone j.C j.K)).obj X).obj a), (Pres.π X i).app a y =
        (Pres.π X j).app a y' → ((hE i).h ≫ (decalage _).map (Pres.π X i)).app a y =
          ((hE j).h ≫ (decalage _).map (Pres.π X j)).app a y' := by
    intro a i j y y' h
    apply Subtype.ext
    obtain ⟨R, hR⟩ := Pres.exists_rootForm F i a.unop y
    obtain ⟨R', hR'⟩ := Pres.exists_rootForm F j a.unop y'
    exact hR.symm.trans ((RootForm.value_eq F R R' (congrArg Subtype.val h)).trans hR')
  obtain ⟨h', hh'⟩ := ExtraDegeneracy.exists_of_jointlySurjective hE (fun i => Pres.π X i)
    hsurj hwd
  have hπ : ∀ i : Pres (m + 1) G, Pres.π X i ≫ P'.ι = (coneRestrictionMap i.q).app X :=
    fun i => Subfunctor.lift_ι _ _
  have hover' := ExtraDegeneracy.h_comp_map_eq_of_jointlySurjective hE (fun i => Pres.π X i)
    (P'.ι ≫ (coneRestrictionMap (outputVertex G)).app X) (pointDeg X) hsurj h' hh' (fun i => by
      have e₁ : Pres.π X i ≫ P'.ι ≫ (coneRestrictionMap (outputVertex G)).app X =
          (coneRestrictionMap (outputVertex (cone i.C i.K))).app X := by
        rw [reassoc_of% (hπ i), ← NatTrans.comp_app, ← coneRestrictionMap_comp,
          outputVertex_comp_of_isCollapseHom i.q i.hq]
      calc (hE i).h ≫ (decalage _).map (Pres.π X i ≫ P'.ι ≫
            (coneRestrictionMap (outputVertex G)).app X) =
          (hE i).h ≫
            (decalage _).map ((coneRestrictionMap (outputVertex (cone i.C i.K))).app X) := by
            rw [e₁]
        _ = (coneRestrictionMap (outputVertex (cone i.C i.K))).app X ≫ (pointDeg X).h :=
            F.coneDeg_over i.C i.hC i.hm i.K
        _ = _ := by rw [← e₁]; simp only [Category.assoc])
  obtain ⟨h, hι, hover⟩ := ExtraDegeneracy.exists_extension
    ((coneRestrictionMap (outputVertex G)).app X) (hX G hG) (pointDeg X) P' h'
    (by rw [hover', Category.assoc])
  refine ⟨h, hover, fun a x hx => ?_, fun C hC hm K q hq => ?_⟩
  · have e : h.h.app a x = (h'.h.app a ⟨x, hx⟩).1 :=
      ConcreteCategory.congr_hom (NatTrans.congr_app hι a) ⟨x, hx⟩
    exact e ▸ (h'.h.app a ⟨x, hx⟩).2
  · rw [← hπ ⟨C, hC, hm, K, q, hq⟩, Category.assoc, hι, reassoc_of% (hh' ⟨C, hC, hm, K, q, hq⟩),
      ← Functor.map_comp]

private lemma dimension_lt_of_isCollapseHom {C C' : Atom} {K : ℕ} (q : C ⟶ cone C' K)
    (hq : IsCollapseHom q) (hiso : ¬ IsIso q) : C'.dimension < C.dimension := by
  have h := dimension_le_of_isCollapseHom q hq
  rw [dimension_cone] at h
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · rcases lt_or_eq_of_le h with h | h
    · simpa using h
    · exact absurd (isIso_of_isCollapseHom_of_dimension_eq q hq h.symm) hiso
  · omega

private lemma coneDeg_congr {X : DiagSet.{u}} {m m' : ℕ}
    {deg : ∀ C : Atom, IsRep C → C.dimension < m →
      ExtraDegeneracy ((coneRestriction C).obj X)}
    {deg' : ∀ C : Atom, IsRep C → C.dimension < m' →
      ExtraDegeneracy ((coneRestriction C).obj X)}
    {C : Atom} (hC : IsRep C) (hm : C.dimension < m) (hm' : C.dimension < m')
    (h : deg C hC hm = deg' C hC hm') (K : ℕ) :
    coneDeg X deg C hC hm K = coneDeg X deg' C hC hm' K := by
  cases K with
  | zero => exact h
  | succ K => rfl

private lemma IsRep.eq_atomPoint {C : Atom} (hC : IsRep C) (hd : C.dimension < 2) :
    C = atomPoint := by
  rcases hC with h | ⟨hcore, h0, -⟩
  · exact h
  · have := (isCore_iff_dimension_eq_zero (by omega)).1 hcore
    omega

private def familyTwo (X : DiagSet.{u}) : Family X 2 where
  deg C hC hm := (hC.eq_atomPoint hm).symm ▸ pointDeg X
  deg_atomPoint _ _ := rfl
  over C hC hm := by
    obtain rfl := hC.eq_atomPoint hm
    exact pointDeg_over X
  compat C hC hm C' hC' hm' K q hq hiso := by
    obtain rfl := hC.eq_atomPoint hm
    have := dimension_lt_of_isCollapseHom q hq hiso
    rw [dimension_atomPoint] at this
    omega

private lemma nonempty_family (X : DiagSet.{u})
    (hX : ∀ G : Atom, IsCore G → ∀ a,
      HasLiftingProperty (boundary a).ι ((coneRestrictionMap (outputVertex G)).app X)) :
    ∀ m, 2 ≤ m → Nonempty (Family X m) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact ⟨familyTwo X⟩
  | succ m hm ih =>
    obtain ⟨F⟩ := ih
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    choose H hover _ hcompat using fun (C : Atom) (hC : IsRep C) =>
      exists_extraDegeneracy_step X hX hC.isCore F
    let deg : ∀ C : Atom, IsRep C → C.dimension < m' + 1 + 1 →
        ExtraDegeneracy ((coneRestriction C).obj X) := fun C hC _ =>
      if h : C.dimension < m' + 1 then F.deg C hC h else H C hC
    have hdeg : ∀ C hC (h : C.dimension < m' + 1) h', deg C hC h' = F.deg C hC h :=
      fun C hC h h' => dif_pos h
    refine ⟨{ deg := deg
              deg_atomPoint := fun hC hm => ?_
              over := fun C hC hm => ?_
              compat := fun C hC hm C' hC' hm' K q hq hiso => ?_ }⟩
    · rw [hdeg atomPoint hC (by rw [dimension_atomPoint]; omega) hm]
      exact F.deg_atomPoint _ _
    · by_cases h : C.dimension < m' + 1
      · rw [hdeg C hC h hm]
        exact F.over C hC h
      · simp only [deg, dif_neg h]
        exact hover C hC
    · have hlt := dimension_lt_of_isCollapseHom q hq hiso
      have hm'' : C'.dimension < m' + 1 := by omega
      rw [coneDeg_congr hC' hm' hm'' (hdeg C' hC' hm'' hm') K]
      by_cases h : C.dimension < m' + 1
      · rw [hdeg C hC h hm]
        exact F.compat C hC h C' hC' hm'' K q hq hiso
      · simp only [deg, dif_neg h]
        exact hcompat C hC C' hC' hm'' K q hq

theorem nonempty_coherentContraction (X : DiagSet.{u})
    (hX : ∀ G : Atom, IsCore G → ∀ a,
      HasLiftingProperty (boundary a).ι ((coneRestrictionMap (outputVertex G)).app X))
    (B : Atom) (hB : IsCore B) (hd : 2 ≤ B.dimension) :
    Nonempty (CoherentContraction B X) := by
  obtain ⟨m, hm⟩ : ∃ m, B.dimension = m + 1 := ⟨B.dimension - 1, by omega⟩
  obtain ⟨F⟩ := nonempty_family X hX (m + 1) (by omega)
  obtain ⟨h, hover, hlow, -⟩ := exists_extraDegeneracy_step X hX hB F
  have hm' : B.dimension - 1 = m := by omega
  refine ⟨{ toExtraDegeneracy := h
            mem_coreFiltration := fun y x hx => ?_
            map_coneMap_outputVertex := fun x => ?_ }⟩
  · rw [hm'] at hx ⊢
    exact hlow y x hx
  · have key := ConcreteCategory.congr_hom (NatTrans.congr_app hover (op WithInitial.star)) x
    have hκ : pointAlgebra.κ WithInitial.star = toAtomPoint (cone atomPoint 1) :=
      @Subsingleton.elim (cone atomPoint 1 ⟶ atomPoint) _ _ _
    refine key.trans ?_
    exact congrArg (fun φ : cone atomPoint 1 ⟶ atomPoint =>
      X.map φ.op (X.map (outputVertex B).op x)) hκ

end Atoms.Diagrammatic

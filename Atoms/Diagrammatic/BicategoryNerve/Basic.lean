import Atoms.Diagrammatic.DiagrammaticSet
import Atoms.Molecule.Labelling
import Atoms.Diagrammatic.RealizationColimits

open CategoryTheory Opposite Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape
open CategoryTheory.Bicategory (pathComp)

universe w v u

namespace Atoms.Diagrammatic

variable (B : Type u) [Bicategory.{w, v} B]

private theorem hom_hom_id (U : Atom) :
    Map.id U.ogp = ConcreteCategory.hom (C := RDCpxDown) (𝟙 U : U ⟶ U).hom.hom :=
  Map.ext fun _ => rfl

private theorem hom_hom_comp {U V W : Atom} (f : U ⟶ V) (g : V ⟶ W) :
    (ConcreteCategory.hom (C := RDCpxDown) g.hom.hom).comp
        (ConcreteCategory.hom (C := RDCpxDown) f.hom.hom) =
      ConcreteCategory.hom (C := RDCpxDown) (f ≫ g).hom.hom :=
  Map.ext fun _ => rfl

def bicategoryNerve : DiagSet.{max u v w} where
  obj U := {ℓ : Labelling B U.unop.ogp U.unop.isRDC // ℓ.IsCommutative}
  map {U V} f := ↾fun ℓ =>
    haveI := Atom.functor_isFibered f.unop
    ⟨ℓ.1.comap (P := V.unop.ogp) (Q := U.unop.ogp)
      (ConcreteCategory.hom (C := RDCpxDown) f.unop.hom.hom) V.unop.isRDC, ℓ.2.comap _⟩
  map_id U := by
    ext ℓ : 3
    apply Subtype.ext
    exact ((congrArg (ℓ.1.comap (P := U.unop.ogp) (Q := U.unop.ogp) · U.unop.isRDC)
      (hom_hom_id U.unop).symm).trans (Labelling.comap_id _))
  map_comp {U V W} f g := by
    ext ℓ : 3
    apply Subtype.ext
    exact ((congrArg (ℓ.1.comap (P := W.unop.ogp) (Q := U.unop.ogp) · W.unop.isRDC)
      (hom_hom_comp g.unop f.unop).symm).trans
        (Labelling.comap_comp (P := W.unop.ogp) (Q := V.unop.ogp) (R := U.unop.ogp) _ _ _))

theorem bicategoryNerve_obj (U : Atom) :
    (bicategoryNerve B).obj (op U) = {ℓ : Labelling B U.ogp U.isRDC // ℓ.IsCommutative} :=
  rfl

theorem bicategoryNerve_map {U V : Atom} (f : U ⟶ V) (ℓ : (bicategoryNerve B).obj (op V)) :
    ((bicategoryNerve B).map f.op ℓ).1 =
      ℓ.1.comap (P := U.ogp) (Q := V.ogp) (ConcreteCategory.hom (C := RDCpxDown) f.hom.hom)
        U.isRDC :=
  rfl

section HomEquiv

variable (P : RDCpx.{0}) [FinEnum P.obj.toOGP] [DecidableLE P.obj.toOGP]

private abbrev incl (x : P.obj.toOGP) : Map (principalAtomRDC P x).ogp P.obj.toOGP :=
  ConcreteCategory.hom (C := RDCpxDown) (principalInclusionRDC P x).hom

private theorem grade_incl (x : P.obj.toOGP) (p : (principalAtomRDC P x).ogp) :
    grade ℕ (incl P x p) = grade ℕ p :=
  (isMorphism (principalInclusionOGP P x)).grade_eq p

private theorem incl_vertex (x : P.obj.toOGP) (α : Bool) {v : P.obj.toOGP}
    (hv : P.obj.toOGP.boundary (.Iic x) 0 α = .Iic v) :
    incl P x (vertex (.Iic (principalAtomRDC P x).top)
      ((principalAtomRDC P x).isRDC (principalAtomRDC P x).top) α) = v := by
  have h := (incl P x).boundary_Iic_apply (boundary_zero_eq_Iic_vertex _
    ((principalAtomRDC P x).isRDC (principalAtomRDC P x).top) α)
  rw [principalInclusionRDC_top P x, hv] at h
  exact (LowerSet.Iic_injective h).symm

private abbrev principalMap {a b : P.obj.toOGP} (hab : a ≤ b) :
    Map (principalAtomRDC P a).ogp (principalAtomRDC P b).ogp :=
  ConcreteCategory.hom (C := RDCpxDown) (principalMapRDC P hab).hom.hom

private theorem incl_principalMap {a b : P.obj.toOGP} (hab : a ≤ b)
    (p : (principalAtomRDC P a).ogp) : incl P b (principalMap P hab p) = incl P a p :=
  congrArg (fun k : atomToRDCpx.obj (principalAtomRDC P a) ⟶ P => ConcreteCategory.hom k.hom p)
    (principalMapRDC_comp_principalInclusionRDC P hab)

private theorem grade_principalMap {a b : P.obj.toOGP} (hab : a ≤ b)
    (p : (principalAtomRDC P a).ogp) : grade ℕ (principalMap P hab p) = grade ℕ p := by
  rw [← grade_incl P b, incl_principalMap, grade_incl]

private theorem principalMap_eq {a b : P.obj.toOGP} (hab : a ≤ b) {p : (principalAtomRDC P a).ogp}
    {q : (principalAtomRDC P b).ogp} (h : incl P a p = incl P b q) : principalMap P hab p = q :=
  injective_principalInclusionRDC P b ((incl_principalMap P hab p).trans h)

variable {P} {B} (φ : realize.{max u v w}.obj P ⟶ bicategoryNerve B)

private abbrev cellLab (x : P.obj.toOGP) :
    Labelling B (principalAtomRDC P x).ogp (principalAtomRDC P x).isRDC :=
  (φ.app (op (principalAtomRDC P x)) ⟨principalInclusionRDC P x⟩).1

private theorem app_comp_principalInclusionRDC (x : P.obj.toOGP) {T : Atom}
    (g : T ⟶ principalAtomRDC P x) :
    (φ.app (op T) ⟨atomToRDCpx.map g ≫ principalInclusionRDC P x⟩).1 =
      (cellLab φ x).comap (P := T.ogp) (Q := (principalAtomRDC P x).ogp)
        (ConcreteCategory.hom (C := RDCpxDown) g.hom.hom) T.isRDC :=
  congrArg Subtype.val (NatTrans.naturality_apply φ g.op ⟨principalInclusionRDC P x⟩)

private theorem cellLab_eq_comap {a b : P.obj.toOGP} (hab : a ≤ b) :
    cellLab φ a = (cellLab φ b).comap (principalMap P hab) (principalAtomRDC P a).isRDC := by
  have h := app_comp_principalInclusionRDC φ b (principalMapRDC P hab)
  rwa [principalMapRDC_comp_principalInclusionRDC] at h

private def nerveObj (v : P.obj.toOGP) : B :=
  (cellLab φ v).toPrefunctor.obj (principalAtomRDC P v).top

private theorem cellLab_obj (x : P.obj.toOGP) (p : (principalAtomRDC P x).ogp) :
    (cellLab φ x).toPrefunctor.obj p = nerveObj φ (incl P x p) := by
  have hle : incl P x p ≤ x := principalInclusionRDC_mem_closure P x p
  have h := congrArg (fun L : Labelling B _ _ => L.toPrefunctor.obj (principalAtomRDC P _).top)
    (cellLab_eq_comap φ hle)
  exact (congrArg (cellLab φ x).toPrefunctor.obj
    (principalMap_eq P hle (principalInclusionRDC_top P _))).symm.trans h.symm

private def topEdge {v w : EdgeQuiver P.obj.toOGP} (e : v ⟶ w) :
    Quiver.Hom (V := EdgeQuiver (principalAtomRDC P e.1).ogp)
      (vertex (.Iic (principalAtomRDC P e.1).top)
        ((principalAtomRDC P e.1).isRDC (principalAtomRDC P e.1).top) false)
      (vertex (.Iic (principalAtomRDC P e.1).top)
        ((principalAtomRDC P e.1).isRDC (principalAtomRDC P e.1).top) true) :=
  ⟨(principalAtomRDC P e.1).top,
    (grade_incl P e.1 _).symm.trans ((congrArg (grade ℕ) (principalInclusionRDC_top P e.1)).trans
      e.2.1),
    boundary_zero_eq_Iic_vertex _ _ false, boundary_zero_eq_Iic_vertex _ _ true⟩

private def nerveMap {v w : EdgeQuiver P.obj.toOGP} (e : v ⟶ w) : nerveObj φ v ⟶ nerveObj φ w :=
  Quiver.homOfEq ((cellLab φ e.1).toPrefunctor.map (topEdge e))
    ((cellLab_obj φ e.1 _).trans (congrArg (nerveObj φ) (incl_vertex P e.1 false e.2.2.1)))
    ((cellLab_obj φ e.1 _).trans (congrArg (nerveObj φ) (incl_vertex P e.1 true e.2.2.2)))

private def nervePrefunctor : Prefunctor (EdgeQuiver P.obj.toOGP) B where
  obj := nerveObj φ
  map := nerveMap φ

private theorem map_heq_of_val_eq {R : OGP.{0}} (F : Prefunctor (EdgeQuiver R) B)
    {a b a' b' : EdgeQuiver R} (e : a ⟶ b) (e' : a' ⟶ b') (ha : a = a') (hb : b = b')
    (h : e.1 = e'.1) : F.map e ≍ F.map e' := by
  subst ha hb
  obtain rfl : e = e' := Subtype.ext h
  rfl

private theorem cellLab_toPrefunctor (x : P.obj.toOGP) :
    (cellLab φ x).toPrefunctor =
      (incl P x).freePrefunctor ⋙q (FreeBicategory.lift (nervePrefunctor φ)).toPrefunctor := by
  refine Prefunctor.hext (cellLab_obj φ x) fun p q d => ?_
  have hd : grade ℕ (incl P x d.1) = 1 := (grade_incl P x _).trans d.2.1
  have hle : incl P x d.1 ≤ x := principalInclusionRDC_mem_closure P x d.1
  have htop : principalMap P hle (principalAtomRDC P _).top = d.1 :=
    principalMap_eq P hle (principalInclusionRDC_top P _)
  have hg : grade ℕ (principalMap P hle (topEdge ((incl P x).mapEdge d hd)).1) = 1 :=
    (grade_principalMap P hle _).trans (topEdge ((incl P x).mapEdge d hd)).2.1
  have hm : (cellLab φ (incl P x d.1)).toPrefunctor.map (topEdge ((incl P x).mapEdge d hd)) ≍
      (cellLab φ x).toPrefunctor.map
        ((principalMap P hle).mapEdge (topEdge ((incl P x).mapEdge d hd)) hg) := by
    refine (congr_arg_heq (fun L : Labelling B _ _ => L.toPrefunctor.map
      (topEdge ((incl P x).mapEdge d hd))) (cellLab_eq_comap φ hle)).trans ?_
    refine heq_of_eq ?_
    change (FreeBicategory.lift (cellLab φ x).toPrefunctor).map
      ((principalMap P hle).freePrefunctor.map _) = _
    rw [(principalMap P hle).freePrefunctor_map_of_grade_eq _ hg]
    rfl
  refine (hm.trans (map_heq_of_val_eq _ _ d (principalMap_eq P hle ?_) (principalMap_eq P hle ?_)
    htop)).symm.trans ?_
  · exact incl_vertex P _ false ((incl P x).boundary_Iic_apply d.2.2.1)
  · exact incl_vertex P _ true ((incl P x).boundary_Iic_apply d.2.2.2)
  change _ ≍ (FreeBicategory.lift (nervePrefunctor φ)).map ((incl P x).freePrefunctor.map d)
  rw [(incl P x).freePrefunctor_map_of_grade_eq d hd]
  exact (Quiver.homOfEq_heq _ _ _).symm

private theorem hom_pathComp_congr {R : OGP.{0}} [Fintype R] [DecidableLE R] (hR : R.IsRDC)
    (G : Prefunctor (EdgeQuiver R) B) {y y' : R} (hy : y = y') {a b s t : R} (ha : a = s)
    (hb : b = t) (h₁ : R.boundary (R.boundary (.Iic y) 1 false) 0 false = .Iic a)
    (h₂ : R.boundary (R.boundary (.Iic y) 1 false) 0 true = .Iic b)
    (h₃ : R.boundary (R.boundary (.Iic y) 1 true) 0 false = .Iic a)
    (h₄ : R.boundary (R.boundary (.Iic y) 1 true) 0 true = .Iic b)
    (h₅ : R.boundary (R.boundary (.Iic y') 1 false) 0 false = .Iic s)
    (h₆ : R.boundary (R.boundary (.Iic y') 1 false) 0 true = .Iic t)
    (h₇ : R.boundary (R.boundary (.Iic y') 1 true) 0 false = .Iic s)
    (h₈ : R.boundary (R.boundary (.Iic y') 1 true) 0 true = .Iic t) :
    (pathComp G (pathOf (R.boundary (.Iic y) 1 false) ((hR y).boundary 1 false)
        ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one) h₁ h₂) ⟶
      pathComp G (pathOf (R.boundary (.Iic y) 1 true) ((hR y).boundary 1 true)
        ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one) h₃ h₄)) =
    (pathComp G (pathOf (R.boundary (.Iic y') 1 false) ((hR y').boundary 1 false)
        ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one) h₅ h₆) ⟶
      pathComp G (pathOf (R.boundary (.Iic y') 1 true) ((hR y').boundary 1 true)
        ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one) h₇ h₈)) := by
  subst hy ha hb
  rfl

private theorem grade_top {x : P.obj.toOGP} {n : ℕ} (hx : grade ℕ x = n) :
    grade ℕ (principalAtomRDC P x).top = n :=
  (grade_incl P x _).symm.trans ((congrArg (grade ℕ) (principalInclusionRDC_top P x)).trans hx)

private def nerveCell (x : P.obj.toOGP) (hx : grade ℕ x = 2) {s t : P.obj.toOGP}
    (hs : P.obj.toOGP.boundary (.Iic x) 0 false = .Iic s)
    (ht : P.obj.toOGP.boundary (.Iic x) 0 true = .Iic t) :
    pathComp (nervePrefunctor φ) (pathOf (P.obj.toOGP.boundary (.Iic x) 1 false)
        ((P.obj.isRDC x).boundary 1 false) ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
        (((P.obj.isRDC x).isGlobular.boundary_boundary_eq_of_le zero_le_one
          (.inl zero_lt_one)).trans hs)
        (((P.obj.isRDC x).isGlobular.boundary_boundary_eq_of_le zero_le_one
          (.inl zero_lt_one)).trans ht)) ⟶
      pathComp (nervePrefunctor φ) (pathOf (P.obj.toOGP.boundary (.Iic x) 1 true)
        ((P.obj.isRDC x).boundary 1 true) ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        (((P.obj.isRDC x).isGlobular.boundary_boundary_eq_of_le zero_le_one
          (.inl zero_lt_one)).trans hs)
        (((P.obj.isRDC x).isGlobular.boundary_boundary_eq_of_le zero_le_one
          (.inl zero_lt_one)).trans ht)) :=
  cast (by
    have hcol {a b : EdgeQuiver (principalAtomRDC P x).ogp} (q : Quiver.Path a b) :
        ∀ e ∈ pathEdges q, grade ℕ (incl P x e) = 1 := fun e he =>
      (grade_incl P x e).trans (grade_of_mem_pathEdges q he)
    rw [cellLab_toPrefunctor φ x,
      Map.pathComp_freePrefunctor_comp_lift_of_forall _ _ _ (hcol _),
      Map.pathComp_freePrefunctor_comp_lift_of_forall _ _ _ (hcol _),
      Map.mapPath_pathOf_boundary _ (principalAtomRDC P x).isRDC P.obj.isRDC,
      Map.mapPath_pathOf_boundary _ (principalAtomRDC P x).isRDC P.obj.isRDC]
    exact hom_pathComp_congr P.obj.isRDC _ (principalInclusionRDC_top P x)
      (incl_vertex P x false hs) (incl_vertex P x true ht) _ _ _ _ _ _ _ _)
    ((cellLab φ x).cell (principalAtomRDC P x).top (grade_top hx)
      (boundary_zero_eq_Iic_vertex _ _ false) (boundary_zero_eq_Iic_vertex _ _ true))

private def nerveLabelling : Labelling B P.obj.toOGP P.obj.isRDC where
  toPrefunctor := nervePrefunctor φ
  obj_eq_of_boundary_Iic x _ hv := ((cellLab φ x).obj_eq_obj_vertex _).trans
    ((cellLab_obj φ x _).trans (congrArg (nerveObj φ) (incl_vertex P x false hv)))
  cell x hx _ _ hs ht := nerveCell φ x hx hs ht

private theorem cellLab_eq_comap_incl (x : P.obj.toOGP) :
    cellLab φ x = (nerveLabelling φ).comap (incl P x) (principalAtomRDC P x).isRDC := by
  refine Labelling.ext (cellLab_toPrefunctor φ x) fun p hp s t hs ht => ?_
  have hle : incl P x p ≤ x := principalInclusionRDC_mem_closure P x p
  have hgr (d : (principalAtomRDC P _).ogp) (_ : d ≤ (principalAtomRDC P (incl P x p)).top) :
      grade ℕ (principalMap P hle d) = grade ℕ d := grade_principalMap P hle d
  have hgr' (d : (principalAtomRDC P x).ogp) (_ : d ≤ p) : grade ℕ (incl P x d) = grade ℕ d :=
    grade_incl P x d
  have hp' : grade ℕ (incl P x p) = 2 := (grade_incl P x p).trans hp
  have hv (α : Bool) := boundary_zero_eq_Iic_vertex (.Iic (principalAtomRDC P (incl P x p)).top)
    ((principalAtomRDC P (incl P x p)).isRDC _) α
  have h₁ := Labelling.conjEqToHom_comap_cell (hP := (principalAtomRDC P _).isRDC)
    (principalMap P hle) (cellLab φ x) (grade_top hp') hgr (hv false) (hv true)
  have h₂ := Labelling.cell_heq_of_eq (cellLab φ x)
    (principalMap_eq P hle (principalInclusionRDC_top P _))
    ((hgr _ le_rfl).trans (grade_top hp')) hp ((principalMap P hle).boundary_Iic_apply (hv false))
    ((principalMap P hle).boundary_Iic_apply (hv true)) hs ht
  have h₃ := congr_arg_heq (fun L : Labelling B _ _ => L.cell _ (grade_top hp') (hv false)
    (hv true)) (cellLab_eq_comap φ hle)
  have h₄ := Labelling.conjEqToHom_comap_cell (hP := (principalAtomRDC P x).isRDC) (incl P x)
    (nerveLabelling φ) hp hgr' hs ht
  exact h₂.symm.trans (h₁.heq.symm.trans (h₃.symm.trans ((cast_heq _ _).symm.trans h₄.heq.symm)))

private theorem isCommutative_nerveLabelling : (nerveLabelling φ).IsCommutative := by
  intro y hy s t hs ht xs ys hxs hys
  have hL := (φ.app (op (principalAtomRDC P y)) ⟨principalInclusionRDC P y⟩).2
  change (cellLab φ y).IsCommutative at hL
  rw [cellLab_eq_comap_incl φ y] at hL
  have hT := (principalAtomRDC P y).isRDC (principalAtomRDC P y).top
  obtain rfl := incl_vertex P y false hs
  obtain rfl := incl_vertex P y true ht
  have key (α : Bool) {zs : List P.obj.toOGP}
      (hzs : IsLayerOrder (P.obj.toOGP.boundary (.Iic y) 2 α) zs) :
      ∃ (zs₀ : List (principalAtomRDC P y).ogp) (hzs₀ : IsLayerOrder
        ((principalAtomRDC P y).ogp.boundary (.Iic (principalAtomRDC P y).top) 2 α) zs₀),
        ConjEqToHom ((nerveLabelling φ).compositeAlong ((P.obj.isRDC y).boundary 2 α) hzs
          (((P.obj.isRDC y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans
            hs)
          (((P.obj.isRDC y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans
            ht))
        (((nerveLabelling φ).comap (incl P y) (principalAtomRDC P y).isRDC).compositeAlong
          (hT.boundary 2 α) hzs₀
          ((hT.isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans
            (boundary_zero_eq_Iic_vertex _ hT false))
          ((hT.isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans
            (boundary_zero_eq_Iic_vertex _ hT true))) := by
      obtain ⟨zs₀, hzs₀⟩ := exists_isLayerOrder (hT.boundary 2 α) (hT.krullDim_boundary (by
        rw [LowerSet.krullDim_Iic, grade_top hy]
        exact_mod_cast (show (2 : ℕ) ≤ 3 by norm_num)) α)
      have e : map (principalInclusionOGP P y)
          ((principalAtomRDC P y).ogp.boundary (.Iic (principalAtomRDC P y).top) 2 α) =
          P.obj.toOGP.boundary (.Iic y) 2 α := by
        rw [map_boundary, map_Iic]
        exact congrArg (fun z => P.obj.toOGP.boundary (.Iic z) 2 α) (principalInclusionRDC_top P y)
      classical
      exact ⟨zs₀, hzs₀, ((Labelling.compositeAlong_comap_of_isInclusion
        (principalInclusionOGP P y) (nerveLabelling φ) (hT.boundary 2 α) hzs₀ _ _).trans
          (Labelling.conjEqToHom_compositeAlong _ e _ _ _ hzs _ _ _ _)).symm⟩
  obtain ⟨xs₀, hxs₀, hx⟩ := key false hxs
  obtain ⟨ys₀, hys₀, hy'⟩ := key true hys
  exact ConjEqToHom.eq_of_eq (hx.conj _ _ _ _) (hy'.conj _ _ _ _)
    (hL _ (grade_top hy) (boundary_zero_eq_Iic_vertex _ hT false)
      (boundary_zero_eq_Iic_vertex _ hT true) hxs₀ hys₀)

variable (B P) in
noncomputable def bicategoryNerveHomEquiv :
    (realize.{max u v w}.obj P ⟶ bicategoryNerve B) ≃
      {ℓ : Labelling B P.obj.toOGP P.obj.isRDC // ℓ.IsCommutative} where
  toFun φ := ⟨nerveLabelling φ, isCommutative_nerveLabelling φ⟩
  invFun ℓ :=
    { app T := ↾fun c =>
        haveI : (ConcreteCategory.hom (C := RDCpxDown)
          c.down.hom).isMap.monotone.functor.IsFibered := c.down.2
        ⟨ℓ.1.comap (P := T.unop.ogp) (Q := P.obj.toOGP)
          (ConcreteCategory.hom (C := RDCpxDown) c.down.hom) T.unop.isRDC, ℓ.2.comap _⟩
      naturality T T' f := by
        ext c
        apply Subtype.ext
        exact (congrArg (ℓ.1.comap (P := T'.unop.ogp) (Q := P.obj.toOGP) · T'.unop.isRDC)
          (Map.ext fun _ => rfl)).trans
            (Labelling.comap_comp (P := T'.unop.ogp) (Q := T.unop.ogp) (R := P.obj.toOGP) _ _ _) }
  left_inv φ := by
    ext ⟨T⟩ ⟨c⟩
    apply Subtype.ext
    have hc := principalLiftRDC_comp_principalInclusionRDC P _ c
      (hom_apply_mem_closure_apply_top c)
    refine Eq.trans ?_ (congrArg (fun k => (φ.app (op T) ⟨k⟩).1) hc)
    rw [app_comp_principalInclusionRDC, cellLab_eq_comap_incl, ← Labelling.comap_comp]
    exact congrArg ((nerveLabelling φ).comap (P := T.ogp) (Q := P.obj.toOGP) · T.isRDC)
      (Map.ext fun t => (congrArg (fun k : atomToRDCpx.obj T ⟶ P => ConcreteCategory.hom k.hom t)
        hc).symm)
  right_inv ℓ := by
    apply Subtype.ext
    refine Labelling.ext (Prefunctor.hext (fun v => congrArg ℓ.1.toPrefunctor.obj
      (principalInclusionRDC_top P v)) fun v w e => ?_) fun x hx s t hs ht => ?_
    · have he : grade ℕ (incl P e.1 (topEdge e).1) = 1 := (grade_incl P _ _).trans (topEdge e).2.1
      refine (Quiver.homOfEq_heq _ _ _).trans ?_
      change (FreeBicategory.lift ℓ.1.toPrefunctor).map
        ((incl P e.1).freePrefunctor.map (topEdge e)) ≍ _
      rw [(incl P e.1).freePrefunctor_map_of_grade_eq _ he]
      exact map_heq_of_val_eq _ _ _ (incl_vertex P _ false e.2.2.1)
        (incl_vertex P _ true e.2.2.2) (principalInclusionRDC_top P e.1)
    · refine (cast_heq _ _).trans ((Labelling.conjEqToHom_comap_cell (incl P x) ℓ.1 (grade_top hx)
        (fun d _ => grade_incl P x d) _ _).heq.trans ?_)
      exact Labelling.cell_heq_of_eq _ (principalInclusionRDC_top P x) _ _ _ _ _ _

variable (B) in
theorem bicategoryNerveHomEquiv_symm_app
    (ℓ : {ℓ : Labelling B P.obj.toOGP P.obj.isRDC // ℓ.IsCommutative}) (T : Atom)
    (c : atomToRDCpx.obj T ⟶ P) :
    (((bicategoryNerveHomEquiv B P).symm ℓ).app (op T) ⟨c⟩).1 =
      ℓ.1.comap (P := T.ogp) (Q := P.obj.toOGP) (ConcreteCategory.hom (C := RDCpxDown) c.hom)
        T.isRDC :=
  rfl

variable (B) in
theorem bicategoryNerveHomEquiv_comp {Q : RDCpx.{0}} [FinEnum Q.obj.toOGP]
    [DecidableLE Q.obj.toOGP] (g : P ⟶ Q) (φ : realize.{max u v w}.obj Q ⟶ bicategoryNerve B) :
    (bicategoryNerveHomEquiv B P (realize.map g ≫ φ)).1 =
      (bicategoryNerveHomEquiv B Q φ).1.comap (P := P.obj.toOGP) (Q := Q.obj.toOGP)
        (ConcreteCategory.hom (C := RDCpxDown) g.hom) P.obj.isRDC := by
  have : (ConcreteCategory.hom (C := RDCpxDown) g.hom).isMap.monotone.functor.IsFibered := g.2
  have h : realize.map g ≫ φ = (bicategoryNerveHomEquiv B P).symm
      ⟨(bicategoryNerveHomEquiv B Q φ).1.comap (P := P.obj.toOGP) (Q := Q.obj.toOGP)
        (ConcreteCategory.hom (C := RDCpxDown) g.hom) P.obj.isRDC,
        (bicategoryNerveHomEquiv B Q φ).2.comap _⟩ := by
    conv_lhs => rw [← (bicategoryNerveHomEquiv B Q).left_inv φ]
    ext ⟨T⟩ ⟨c⟩
    apply Subtype.ext
    exact (congrArg ((bicategoryNerveHomEquiv B Q φ).1.comap (P := T.ogp) (Q := Q.obj.toOGP) ·
      T.isRDC) (Map.ext fun _ => rfl)).trans (Labelling.comap_comp _ _ _)
  rw [h, Equiv.apply_symm_apply]

end HomEquiv

end Atoms.Diagrammatic

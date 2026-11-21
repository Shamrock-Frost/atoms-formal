import Atoms.Diagrammatic.Joyal.FaceNerve
import Atoms.Diagrammatic.Marked.Fibrancy
import Atoms.Homotopical.Simplicial.CartesianInduction

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial Opposite
open Atoms.Homotopical Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open SSet

private abbrev nerveEdge {R : Type} [Preorder R] {a b : R} (h : a ≤ b) :
    (nerve (ULift.{u} R)) _⦋1⦌ :=
  ComposableArrows.mk₁ (homOfLE (ULift.up_le.2 h))

private def NerveInv {R : Type} [Preorder R] {Q : SSet.{u}} (g : nerve (ULift.{u} R) ⟶ Q)
    {a b : R} (h : a ≤ b) : Prop :=
  Nonempty (Edge.mk' (g.app _ (nerveEdge h))).InvStruct

private abbrev nerveTriangle {R : Type} [Preorder R] {a b c : R} (hab : a ≤ b) (hbc : b ≤ c) :
    (nerve (ULift.{u} R)) _⦋2⦌ :=
  ComposableArrows.mk₂ (homOfLE (ULift.up_le.2 hab)) (homOfLE (ULift.up_le.2 hbc))

private theorem nerveInv_iff {R : Type} [Preorder R] {Q : SSet.{u}} [Q.Quasicategory]
    (g : nerve (ULift.{u} R) ⟶ Q) {a b c : R} (hab : a ≤ b) (hbc : b ≤ c) (h : NerveInv g hab) :
    NerveInv g hbc ↔ NerveInv g (hab.trans hbc) := by
  have e (i : Fin 3) (t : (nerve (ULift.{u} R)) _⦋1⦌)
      (ht : (nerve (ULift.{u} R)).δ i (nerveTriangle hab hbc) = t) :
      Q.δ i (g.app _ (nerveTriangle hab hbc)) = g.app _ t := by
    rw [← ht, δ_naturality_apply]
  have e₂ := e 2 (nerveEdge hab) (nerve.ext_of_isThin (by funext i; fin_cases i <;> rfl))
  have e₀ := e 0 (nerveEdge hbc) (nerve.ext_of_isThin (by funext i; fin_cases i <;> rfl))
  have e₁ := e 1 (nerveEdge (hab.trans hbc))
    (nerve.ext_of_isThin (by funext i; fin_cases i <;> rfl))
  let σ := g.app _ (nerveTriangle hab hbc)
  let f₀₁ := Edge.mk' (Q.δ 2 σ)
  let f₁₂ : Edge (Q.δ 0 (Q.δ 2 σ)) (Q.δ 0 (Q.δ 0 σ)) := Edge.mk (Q.δ 0 σ)
    (δ_comp_δ_apply (i := 0) (j := 1) (by decide) σ).symm rfl
  let f₀₂ : Edge (Q.δ 1 (Q.δ 2 σ)) (Q.δ 0 (Q.δ 0 σ)) := Edge.mk (Q.δ 1 σ)
    (δ_comp_δ_self_apply (i := 1) σ) (δ_comp_δ_self_apply (i := 0) σ).symm
  have hc := Truncated.HomotopyCategory.homMk_comp_homMk
    (Edge.CompStruct.mk (e₀₁ := f₀₁) (e₁₂ := f₁₂) (e₀₂ := f₀₂) σ rfl rfl rfl)
  have k₂ : NerveInv g hab ↔ Nonempty f₀₁.InvStruct :=
    ⟨fun ⟨I⟩ ↦ ⟨I.ofEq e₂.symm⟩, fun ⟨I⟩ ↦ ⟨I.ofEq e₂⟩⟩
  have k₀ : NerveInv g hbc ↔ Nonempty f₁₂.InvStruct :=
    ⟨fun ⟨I⟩ ↦ ⟨I.ofEq e₀.symm⟩, fun ⟨I⟩ ↦ ⟨I.ofEq e₀⟩⟩
  have k₁ : NerveInv g (hab.trans hbc) ↔ Nonempty f₀₂.InvStruct :=
    ⟨fun ⟨I⟩ ↦ ⟨I.ofEq e₁.symm⟩, fun ⟨I⟩ ↦ ⟨I.ofEq e₁⟩⟩
  rw [k₀, k₁, ← isIso_homMk_iff, ← isIso_homMk_iff]
  rw [k₂, ← isIso_homMk_iff] at h
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · have : IsIso (Truncated.HomotopyCategory.homMk f₀₂.toTruncated) := by
      rw [← hc]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h h'
    exact this
  · have : IsIso (Truncated.HomotopyCategory.homMk f₀₁.toTruncated ≫
        Truncated.HomotopyCategory.homMk f₁₂.toTruncated) := by
      rw [hc]
      exact h'
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h this

private abbrev outV (P : OGP.{0}) (x : P) : LowerSet P :=
  P.boundary (.Iic x) 0 true

private abbrev cyl (U : Atom) (a : globe.{0} 1) (x : U.ogp) : (grayCylinder.obj U).ogp :=
  (cylAtomIso U).hom (a, x)

private theorem cyl_le {U : Atom} {a b : globe.{0} 1} {x y : U.ogp}
    (hab : a ≤ b) (hxy : x ≤ y) : cyl U a x ≤ cyl U b y :=
  (isMorphism (cylAtomIso U).hom).monotone ⟨hab, hxy⟩

private theorem outV_cyl (U : Atom) (a : globe.{0} 1) (x : U.ogp) :
    outV (grayCylinder.obj U).ogp (cyl U a x) =
      map (cylAtomIso U).hom (outV (globe.{0} 1) a ×ˢ outV U.ogp x) := by
  rw [← boundary_Iic_grayProduct_zero (IsMoleculeIn.isGlobular (isRDC_globe_one a))
    (IsMoleculeIn.isGlobular (U.isRDC x)) true, map_boundary, map_Iic]
  rfl

private theorem outV_cyl_eq {U : Atom} {a b : globe.{0} 1} {x y : U.ogp}
    (hab : outV (globe.{0} 1) a = outV (globe.{0} 1) b) (hxy : outV U.ogp x = outV U.ogp y) :
    outV (grayCylinder.obj U).ogp (cyl U a x) = outV (grayCylinder.obj U).ogp (cyl U b y) := by
  rw [outV_cyl, outV_cyl, hab, hxy]

private theorem exists_outV_eq (U : Atom) (x : U.ogp) :
    ∃ v, v ≤ x ∧ grade ℕ v = 0 ∧ outV U.ogp v = outV U.ogp x := by
  obtain ⟨v, hvmin, hv⟩ := exists_boundary_zero_eq_Iic (U.isRDC x) true
  have hmem : v ∈ U.ogp.boundary (.Iic x) 0 true := hv ▸ LowerSet.mem_Iic_iff.2 le_rfl
  have hd : grade ℕ v = 0 := grade_eq_zero_iff.2 hvmin
  exact ⟨v, LowerSet.mem_Iic_iff.1 (boundary_le _ 0 true hmem), hd,
    (boundary_Iic_of_isMin hvmin 0 true).trans hv.symm⟩

private abbrev gIn (ε : Bool) : globe.{0} 1 := SuspCarrier.pole ε

private abbrev gEdge : globe.{0} 1 := ⊤

private theorem outV_globe_one_inr :
    outV (globe.{0} 1) (gIn true) = outV (globe.{0} 1) gEdge := by
  rw [outV, outV, boundary_Iic_of_isMin (SuspCarrier.isMin_pole true), LowerSet.Iic_top,
    boundary_zero_globe_one]

private theorem globe_one_le_cases {a b : globe.{0} 1} (h : a ≤ b) :
    a = b ∨ (a = gIn false ∧ b = gEdge) ∨ (a = gIn true ∧ b = gEdge) := by
  rcases b with ε | ⟨⟨⟩⟩
  · exact Or.inl ((SuspCarrier.isMin_pole ε).eq_of_le h)
  · rcases a with (_ | _) | ⟨⟨⟩⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inl rfl

private theorem le_gEdge (a : globe.{0} 1) : a ≤ gEdge :=
  le_top

section Inv

variable {U : Atom} {Q : SSet.{u}} [Q.Quasicategory]
  (g : nerve (ULift.{u} (grayCylinder.obj U).ogp) ⟶ Q)

private theorem nerveInv_cyl_inl_false_inr
    (hi : ∀ (z z' : (grayCylinder.obj U).ogp) (h : z ≤ z'),
      outV _ z = outV _ z' → NerveInv g h)
    (hii : ∀ v : U.ogp, grade ℕ v = 0 →
      NerveInv g (cyl_le (le_gEdge (gIn false)) (le_refl v)))
    {x y : U.ogp} (hxy : x ≤ y) (h : outV U.ogp x = outV U.ogp y) :
    NerveInv g (cyl_le (le_gEdge (gIn false)) hxy) := by
  obtain ⟨v, hvx, hd, hv⟩ := exists_outV_eq U x
  have h₁ := nerveInv_iff g (cyl_le (le_gEdge (gIn false)) (le_refl v))
    (cyl_le le_rfl (hvx.trans hxy)) (hii v hd)
  have h₂ := nerveInv_iff g (cyl_le (le_refl (gIn false)) hvx)
    (cyl_le (le_gEdge (gIn false)) hxy) (hi _ _ _ (outV_cyl_eq rfl hv))
  exact h₂.2 (h₁.1 (hi _ _ _ (outV_cyl_eq rfl (hv.trans h))))

private theorem nerveInv_cyl (M : Set U.ogp)
    (hi : ∀ (z z' : (grayCylinder.obj U).ogp) (h : z ≤ z'),
      outV _ z = outV _ z' → NerveInv g h)
    (hii : ∀ v : U.ogp, grade ℕ v = 0 →
      NerveInv g (cyl_le (le_gEdge (gIn false)) (le_refl v)))
    (hiii : ∀ y ∈ M, grade ℕ y = 1 → ∀ (ε : Bool) (x : U.ogp) (hx : x ≤ y),
      NerveInv g (cyl_le (le_refl (gIn ε)) hx))
    {a b : globe.{0} 1} {x y : U.ogp} (hab : a ≤ b) (hxy : x ≤ y)
    (h : outV U.ogp x = outV U.ogp y ∨ y ∈ M ∧ grade ℕ y = 1) :
    NerveInv g (cyl_le hab hxy) := by
  rcases h with h | ⟨hM, hd⟩
  · rcases globe_one_le_cases hab with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hi _ _ _ (outV_cyl_eq rfl h)
    · exact nerveInv_cyl_inl_false_inr g hi hii hxy h
    · exact hi _ _ _ (outV_cyl_eq outV_globe_one_inr h)
  · have hp : NerveInv g (cyl_le (le_gEdge (gIn true)) hxy) :=
      (nerveInv_iff g (cyl_le (le_refl (gIn true)) hxy)
        (cyl_le (le_gEdge (gIn true)) (le_refl y)) (hiii y hM hd true x hxy)).1
        (hi _ _ _ (outV_cyl_eq outV_globe_one_inr rfl))
    rcases globe_one_le_cases hab with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases a with ε | ⟨⟨⟩⟩
      · exact hiii y hM hd ε x hxy
      · exact (nerveInv_iff g (cyl_le (le_gEdge (gIn true)) (le_refl x))
          (cyl_le le_rfl hxy) (hi _ _ _ (outV_cyl_eq outV_globe_one_inr rfl))).2 hp
    · exact (nerveInv_iff g (cyl_le (le_refl (gIn false)) hxy)
        (cyl_le (le_gEdge (gIn false)) (le_refl y)) (hiii y hM hd false x hxy)).1
        (nerveInv_cyl_inl_false_inr g hi hii le_rfl rfl)
    · exact hp

end Inv

section SharpProd

open MonoidalCategory MarkedSSet.modelCategoryCartesian

private def sharpProdObj (S : SSet.{u}) (X : MarkedSSet) : MarkedSSet :=
  MarkedSSet.ofEdges (S ⊗ X.underlying) {e | e.2 ∈ X.marked ⦋1⦌}
    fun x ↦ X.map_σ_mem_marked x.2

private theorem mem_marked_sharpProdObj (S : SSet.{u}) (X : MarkedSSet)
    (e : (S ⊗ X.underlying : SSet) _⦋1⦌) :
    e ∈ (sharpProdObj S X).marked ⦋1⦌ ↔ e.2 ∈ X.marked ⦋1⦌ :=
  MarkedSSet.mem_marked_ofEdges _ _ _ _

private noncomputable def sharpProdProj (S : SSet.{u}) (X : MarkedSSet) : sharpProdObj S X ⟶ X :=
  edgeHomMk (X := sharpProdObj S X) (CartesianMonoidalCategory.snd _ _)
    fun e he ↦ (mem_marked_sharpProdObj S X e).1 he

private noncomputable def sharpProdIncl {S : SSet.{u}} (s : S _⦋0⦌) (X : MarkedSSet) :
    X ⟶ sharpProdObj S X :=
  edgeHomMk (Y := sharpProdObj S X) (CartesianMonoidalCategory.lift (SSet.const s) (𝟙 _))
    fun _ he ↦ (mem_marked_sharpProdObj S X _).2 he

private theorem sharpProdIncl_comp_sharpProdProj {S : SSet.{u}} (s : S _⦋0⦌) (X : MarkedSSet) :
    sharpProdIncl s X ≫ sharpProdProj S X = 𝟙 X :=
  MarkedPresheaf.hom_ext rfl

private def globeContraction :
    ULift.{u} (Fin 2) × globe.{0} 1 →o globe.{0} 1 where
  toFun z := if z.1.down = 0 then z.2 else gEdge
  monotone' z z' h := by
    by_cases h' : z'.1.down = 0
    · have h₀ : z.1.down = 0 := Fin.le_zero_iff.1 (h' ▸ h.1)
      simp only [h₀, h', if_true]
      exact h.2
    · simp only [h', if_false]
      exact le_gEdge _

private def gEdgeVertex : (nerve (ULift.{u} (globe.{0} 1))) _⦋0⦌ :=
  ComposableArrows.mk₀ (ULift.up gEdge)

private noncomputable def sharpProdContraction (X : MarkedSSet) :
    sharpEdgeProdObj (sharpProdObj (nerve (ULift.{u} (globe.{0} 1))) X) ⟶
      sharpProdObj (nerve (ULift.{u} (globe.{0} 1))) X :=
  edgeHomMk (CartesianMonoidalCategory.lift
      ((Δ[1] ◁ CartesianMonoidalCategory.fst _ _) ≫ nerveHomotopy globeContraction)
      (CartesianMonoidalCategory.snd _ _ ≫ CartesianMonoidalCategory.snd _ _))
    fun e he ↦ (mem_marked_sharpProdObj _ X _).2
      ((mem_marked_sharpProdObj _ X e.2).1 ((mem_marked_sharpEdgeProdObj _ e).1 he))

private theorem sharpEdgeEndpoint_zero_app_comp_sharpProdContraction (X : MarkedSSet) :
    (sharpEdgeEndpoint 0).app _ ≫ sharpProdContraction.{u} X = 𝟙 _ :=
  MarkedPresheaf.hom_ext (by
    ext ⟨⟨k⟩⟩ z
    exact Prod.ext (nerve.ext_of_isThin (funext fun i ↦ rfl)) rfl)

private theorem sharpEdgeEndpoint_one_app_comp_sharpProdContraction (X : MarkedSSet) :
    (sharpEdgeEndpoint 1).app _ ≫ sharpProdContraction X =
      sharpProdProj (nerve (ULift.{u} (globe.{0} 1))) X ≫ sharpProdIncl gEdgeVertex X :=
  MarkedPresheaf.hom_ext (by
    ext ⟨⟨k⟩⟩ z
    exact Prod.ext (nerve.ext_of_isThin (funext fun i ↦ rfl)) rfl)

end SharpProd

private theorem mem_marked_nerve_obj_sharp (K : SSet.{u}) {V : Atom} (hV : atomMarking.markable V)
    (c : ((MarkedPresheaf.nerve markedFaceNerveSite epi_markedFaceNerveSite_map_toSelf).obj
      ((MarkedPresheaf.sharp edgeMarking).obj K)).underlying.obj (op V)) :
    c ∈ ((MarkedPresheaf.nerve markedFaceNerveSite epi_markedFaceNerveSite_map_toSelf).obj
      ((MarkedPresheaf.sharp edgeMarking).obj K)).marked V := by
  refine ⟨hV, (MarkedPresheaf.homMk (X := markedFaceNerveSite.obj (MarkedSite.marked V hV))
    (Y := (MarkedPresheaf.sharp edgeMarking).obj K) (MarkedPresheaf.forget.map c)
    fun a _ hx ↦ (MarkedPresheaf.mem_marked_sharp _ _ _ _).2 (MarkedPresheaf.markable _ a _ hx) :
      markedFaceNerveSite.obj (MarkedSite.marked V hV) ⟶ _), ?_⟩
  exact MarkedPresheaf.hom_ext rfl

private noncomputable def homNerveSharpEquiv (Z : MarkedDiagSet.{u}) (K : SSet.{u}) :
    (Z ⟶ (MarkedPresheaf.nerve markedFaceNerveSite epi_markedFaceNerveSite_map_toSelf).obj
      ((MarkedPresheaf.sharp edgeMarking).obj K)) ≃
      (MarkedPresheaf.forget.obj Z ⟶ MarkedPresheaf.forget.obj
        ((MarkedPresheaf.nerve markedFaceNerveSite epi_markedFaceNerveSite_map_toSelf).obj
          ((MarkedPresheaf.sharp edgeMarking).obj K))) where
  toFun := MarkedPresheaf.forget.map
  invFun φ := MarkedPresheaf.homMk φ fun V _ hx ↦
    mem_marked_nerve_obj_sharp K (MarkedPresheaf.markable _ V _ hx) _
  left_inv _ := MarkedPresheaf.hom_ext rfl
  right_inv _ := rfl

private noncomputable def homForgetMarkedFaceNerveEquiv (Z : MarkedDiagSet.{u}) (K : SSet.{u}) :
    (MarkedPresheaf.forget.obj (markedFaceNerve.obj Z) ⟶ K) ≃
      (MarkedPresheaf.forget.obj Z ⟶ MarkedPresheaf.forget.obj
        ((MarkedPresheaf.nerve markedFaceNerveSite epi_markedFaceNerveSite_map_toSelf).obj
          ((MarkedPresheaf.sharp edgeMarking).obj K))) :=
  ((MarkedPresheaf.forgetSharpAdjunction edgeMarking).homEquiv _ _).trans
    ((markedFaceNerveAdjunction.homEquiv _ _).trans (homNerveSharpEquiv Z K))

private theorem homForgetMarkedFaceNerveEquiv_comp {Z Z' : MarkedDiagSet.{u}} (f : Z ⟶ Z')
    {K : SSet.{u}} (φ : MarkedPresheaf.forget.obj (markedFaceNerve.obj Z') ⟶ K) :
    homForgetMarkedFaceNerveEquiv Z K (MarkedPresheaf.forget.map (markedFaceNerve.map f) ≫ φ) =
      MarkedPresheaf.forget.map f ≫ homForgetMarkedFaceNerveEquiv Z' K φ := by
  change MarkedPresheaf.forget.map (markedFaceNerveAdjunction.homEquiv _ _
    ((MarkedPresheaf.forgetSharpAdjunction edgeMarking).homEquiv _ _
      (MarkedPresheaf.forget.map (markedFaceNerve.map f) ≫ φ))) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    Functor.map_comp]
  rfl

private theorem isIso_forget_map_markedFaceNerve_map {Z Z' : MarkedDiagSet.{u}} (f : Z ⟶ Z')
    [IsIso (MarkedPresheaf.forget.map f)] :
    IsIso (MarkedPresheaf.forget.map (markedFaceNerve.map f)) := by
  set u := MarkedPresheaf.forget.map (markedFaceNerve.map f)
  have hbij (K : SSet.{u}) : Function.Bijective
      (fun φ : MarkedPresheaf.forget.obj (markedFaceNerve.obj Z') ⟶ K ↦ u ≫ φ) := by
    have e : (fun φ : MarkedPresheaf.forget.obj (markedFaceNerve.obj Z') ⟶ K ↦ u ≫ φ) =
        (homForgetMarkedFaceNerveEquiv Z K).symm ∘
          (fun ψ ↦ MarkedPresheaf.forget.map f ≫ ψ) ∘ homForgetMarkedFaceNerveEquiv Z' K := by
      funext φ
      exact ((Equiv.symm_apply_eq _).2 (homForgetMarkedFaceNerveEquiv_comp f φ).symm).symm
    rw [e]
    refine (Equiv.bijective _).comp (Function.Bijective.comp ?_ (Equiv.bijective _))
    exact ⟨fun _ _ h ↦ (cancel_epi _).1 h, fun ψ ↦ ⟨inv (MarkedPresheaf.forget.map f) ≫ ψ,
      IsIso.hom_inv_id_assoc _ _⟩⟩
  obtain ⟨v, hv⟩ := (hbij _).2 (𝟙 _)
  replace hv : u ≫ v = 𝟙 _ := hv
  refine ⟨v, hv, (hbij _).1 ?_⟩
  change u ≫ v ≫ u = u ≫ 𝟙 _
  rw [← Category.assoc, hv, Category.id_comp, Category.comp_id]

private noncomputable def cylinderBallMap (w : MarkedSite atomMarking) :
    (MarkedPresheaf.yoneda atomMarking).obj
        ((MarkedSite.unmarked atomMarking).obj (grayCylinder.obj w.obj)) ⟶
      markedCylinderSite.{u}.obj w :=
  MarkedPresheaf.homMk (Y := markedCylinderSite.obj w)
    (ballIsoForgetYoneda ((MarkedSite.unmarked atomMarking).obj (grayCylinder.obj w.obj))).inv
    fun V g hg ↦ (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2 (Or.inl (by
      obtain ⟨-, ⟨h, -⟩ | hd⟩ := (mem_marked_yoneda_obj_iff _ V g).1 hg
      · exact absurd h Bool.false_ne_true
      · exact isDegenerate_ball_of_degenerate hd))

private theorem cylinderBallMap_naturality {w w' : MarkedSite atomMarking} (g : w ⟶ w') :
    (MarkedPresheaf.yoneda atomMarking).map
        ((MarkedSite.unmarked atomMarking).map (grayCylinder.map g.1)) ≫ cylinderBallMap w' =
      cylinderBallMap w ≫ markedCylinderSite.{u}.map g :=
  MarkedPresheaf.hom_ext rfl

private noncomputable def siteFaceNerveIso (x : MarkedSite atomMarking) :
    markedFaceNerveSite.{u}.obj x ≅
      markedFaceNerve.obj ((MarkedPresheaf.yoneda atomMarking).obj x) :=
  ((MarkedPresheaf.yonedaCompExtendIso markedFaceNerveSite).app x).symm

@[reassoc]
private theorem siteFaceNerveIso_hom_naturality {x y : MarkedSite atomMarking} (g : x ⟶ y) :
    markedFaceNerveSite.{u}.map g ≫ (siteFaceNerveIso y).hom =
      (siteFaceNerveIso x).hom ≫ markedFaceNerve.map ((MarkedPresheaf.yoneda atomMarking).map g) :=
  (MarkedPresheaf.yonedaCompExtendIso markedFaceNerveSite).inv.naturality g

private noncomputable def siteCylinderIso (x : MarkedSite atomMarking) :
    markedCylinderSite.{u}.obj x ≅
      markedExactCylinder.I.obj ((MarkedPresheaf.yoneda atomMarking).obj x) :=
  ((MarkedPresheaf.yonedaCompExtendIso markedCylinderSite).app x).symm

@[reassoc]
private theorem siteCylinderIso_hom_naturality {x y : MarkedSite atomMarking} (g : x ⟶ y) :
    markedCylinderSite.{u}.map g ≫ (siteCylinderIso y).hom =
      (siteCylinderIso x).hom ≫
        markedExactCylinder.I.map ((MarkedPresheaf.yoneda atomMarking).map g) :=
  (MarkedPresheaf.yonedaCompExtendIso markedCylinderSite).inv.naturality g

private noncomputable def cylinderSiteFaceNerveMap (w : MarkedSite atomMarking) :
    rdcFaceNerve.{u}.obj (atomToRDCpx.obj (grayCylinder.obj w.obj)) ⟶
      markedFaceNerve.obj (markedCylinderSite.obj w) :=
  unmarkedCompMarkedFaceNerveSiteIso.inv.app (grayCylinder.obj w.obj) ≫
    (siteFaceNerveIso ((MarkedSite.unmarked atomMarking).obj (grayCylinder.obj w.obj))).hom ≫
    markedFaceNerve.map (cylinderBallMap w)

private noncomputable def cylinderFaceNerveMap (w : MarkedSite atomMarking) :
    rdcFaceNerve.{u}.obj (atomToRDCpx.obj (grayCylinder.obj w.obj)) ⟶
      markedFaceNerve.obj (markedExactCylinder.I.obj ((MarkedPresheaf.yoneda atomMarking).obj w)) :=
  cylinderSiteFaceNerveMap w ≫ markedFaceNerve.map (siteCylinderIso w).hom

private instance isIso_forget_map_cylinderFaceNerveMap (w : MarkedSite atomMarking) :
    IsIso (MarkedPresheaf.forget.map (cylinderFaceNerveMap.{u} w)) := by
  have : IsIso (MarkedPresheaf.forget.map (cylinderBallMap w)) :=
    inferInstanceAs (IsIso (ballIsoForgetYoneda _).inv)
  have := isIso_forget_map_markedFaceNerve_map (cylinderBallMap w)
  simp only [cylinderFaceNerveMap, cylinderSiteFaceNerveMap, Functor.map_comp]
  infer_instance

private theorem cylinderFaceNerveMap_naturality {w w' : MarkedSite atomMarking} (g : w ⟶ w') :
    cylinderFaceNerveMap w ≫ markedFaceNerve.{u}.map
        (markedExactCylinder.I.map ((MarkedPresheaf.yoneda atomMarking).map g)) =
      rdcFaceNerve.map (atomToRDCpx.map (grayCylinder.map g.1)) ≫ cylinderFaceNerveMap w' := by
  have h₃ : rdcFaceNerve.map (atomToRDCpx.map (grayCylinder.map g.1)) ≫
      unmarkedCompMarkedFaceNerveSiteIso.inv.app _ =
      unmarkedCompMarkedFaceNerveSiteIso.inv.app _ ≫
        markedFaceNerveSite.map ((MarkedSite.unmarked atomMarking).map (grayCylinder.map g.1)) :=
    unmarkedCompMarkedFaceNerveSiteIso.inv.naturality _
  have h₄ := congrArg markedFaceNerve.map (cylinderBallMap_naturality g)
  rw [Functor.map_comp, Functor.map_comp] at h₄
  simp only [cylinderFaceNerveMap, cylinderSiteFaceNerveMap, Category.assoc]
  rw [← Functor.map_comp markedFaceNerve _ (markedExactCylinder.I.map _),
    ← siteCylinderIso_hom_naturality, Functor.map_comp, reassoc_of% h₃,
    siteFaceNerveIso_hom_naturality_assoc, reassoc_of% h₄]

private noncomputable def cylinderMarkedCellMap (w : MarkedSite atomMarking) {V : Atom}
    (hV : atomMarking.markable V) (c : V ⟶ grayCylinder.obj w.obj)
    (hc : c V.top ∈ cylinderMarked w) :
    (MarkedPresheaf.yoneda atomMarking).obj (MarkedSite.marked V hV) ⟶
      markedCylinderSite.obj w :=
  MarkedPresheaf.homMk (Y := markedCylinderSite.obj w)
    { app V' := ↾fun g ↦ (ULift.up (g.down.1 ≫ c) : ULift.{u} (V'.unop ⟶ grayCylinder.obj w.obj))
      naturality _ _ _ := rfl }
    fun V' g hg ↦ (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 (by
      obtain ⟨-, ⟨-, hi⟩ | hd⟩ := (mem_marked_yoneda_obj_iff _ V' g).1 hg
      · have key : ∀ f : V' ⟶ V, IsIso f → (f ≫ c) V'.top ∈ cylinderMarked w := fun f _ ↦ by
          have hf : f V'.top = V.top := iso_hom_apply_top (asIso f)
          rw [ConcreteCategory.comp_apply, hf]
          exact hc
        exact Or.inr (key g.down.1 hi)
      · exact Or.inl (isDegenerate_ball_of_degenerate (hd.comp c)))

private theorem yoneda_map_toSelf_comp_cylinderMarkedCellMap (w : MarkedSite atomMarking)
    {V : Atom} (hV : atomMarking.markable V) (c : V ⟶ grayCylinder.obj w.obj)
    (hc : c V.top ∈ cylinderMarked w) :
    (MarkedPresheaf.yoneda atomMarking).map (MarkedSite.toSelf (MarkedSite.marked V hV)) ≫
        cylinderMarkedCellMap.{u} w hV c hc =
      (MarkedPresheaf.yoneda atomMarking).map ((MarkedSite.unmarked atomMarking).map c) ≫
        cylinderBallMap w :=
  MarkedPresheaf.hom_ext rfl

private theorem cylinderSiteFaceNerveMap_mem_marked (w : MarkedSite atomMarking) {V : Atom}
    (hV : atomMarking.markable V) (hV₁ : V.dimension = 1) (c : V ⟶ grayCylinder.obj w.obj)
    (hc : c V.top ∈ cylinderMarked w) (x₀ : V.ogp) :
    (MarkedPresheaf.forget.map (rdcFaceNerve.{u}.map (atomToRDCpx.map c) ≫
      cylinderSiteFaceNerveMap w)).app _ (nerveEdge (V.le_top x₀)) ∈
        (markedFaceNerve.obj (markedCylinderSite.obj w)).marked ⦋1⦌ := by
  have h₁ : rdcFaceNerve.map (atomToRDCpx.map c) ≫
      unmarkedCompMarkedFaceNerveSiteIso.inv.app _ =
      unmarkedCompMarkedFaceNerveSiteIso.inv.app _ ≫
        markedFaceNerveSite.map ((MarkedSite.unmarked atomMarking).map c) :=
    unmarkedCompMarkedFaceNerveSiteIso.inv.naturality c
  have h₂ : markedFaceNerve.map
        ((MarkedPresheaf.yoneda atomMarking).map (MarkedSite.toSelf (MarkedSite.marked V hV))) ≫
        markedFaceNerve.map (cylinderMarkedCellMap w hV c hc) =
      markedFaceNerve.map ((MarkedPresheaf.yoneda atomMarking).map
        ((MarkedSite.unmarked atomMarking).map c)) ≫ markedFaceNerve.map (cylinderBallMap w) :=
    (markedFaceNerve.map_comp _ _).symm.trans ((congrArg markedFaceNerve.map
      (yoneda_map_toSelf_comp_cylinderMarkedCellMap w hV c hc)).trans
        (markedFaceNerve.map_comp _ _))
  have heq : rdcFaceNerve.map (atomToRDCpx.map c) ≫ cylinderSiteFaceNerveMap w =
      unmarkedCompMarkedFaceNerveSiteIso.inv.app _ ≫
        markedFaceNerveSite.map (MarkedSite.toSelf (MarkedSite.marked V hV)) ≫
        (siteFaceNerveIso _).hom ≫ markedFaceNerve.map (cylinderMarkedCellMap w hV c hc) := by
    rw [cylinderSiteFaceNerveMap, reassoc_of% h₁, siteFaceNerveIso_hom_naturality_assoc, ← h₂,
      siteFaceNerveIso_hom_naturality_assoc]
    rfl
  have hm : nerveEdge (V.le_top x₀) ∈
      (markedFaceNerveSite.obj (MarkedSite.marked V hV)).marked ⦋1⦌ :=
    (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
      ⟨rfl, Or.inr ⟨⟨rfl, fun z _ ↦ V.le_top z⟩, V.dimension_eq.symm.trans hV₁⟩⟩
  rw [heq]
  exact MarkedPresheaf.map_mem_marked
    ((siteFaceNerveIso _).hom ≫ markedFaceNerve.map (cylinderMarkedCellMap w hV c hc)) hm

private def grayContractionSite (w : MarkedSite atomMarking) :
    (MarkedSite.unmarked atomMarking).obj (grayCylinder.obj w.obj) ⟶ w :=
  ⟨grayContraction.app w.obj, fun h ↦ absurd h Bool.false_ne_true⟩

private theorem siteCylinderIso_hom_comp_contraction (w : MarkedSite atomMarking) :
    (siteCylinderIso w).hom ≫
        markedExactCylinder.{u}.contraction.app ((MarkedPresheaf.yoneda atomMarking).obj w) =
      markedCylinderSiteContraction.app w := by
  have h₁ := MarkedPresheaf.extendMap_app_yoneda_obj markedCylinderSiteContraction w
  have h₂ : (MarkedPresheaf.yonedaCompExtendIso (MarkedPresheaf.yoneda atomMarking)).inv.app w ≫
      (MarkedPresheaf.extendYonedaIso atomMarking).hom.app _ = 𝟙 _ := by
    rw [← MarkedPresheaf.extendYonedaIso_inv_app_yoneda_obj, Iso.inv_hom_id_app]
    rfl
  refine (congrArg ((siteCylinderIso w).hom ≫ ·)
    (congrArg (· ≫ (MarkedPresheaf.extendYonedaIso atomMarking).hom.app _) h₁)).trans ?_
  refine (congrArg ((siteCylinderIso w).hom ≫ ·) (Category.assoc _ _ _)).trans ?_
  refine (Iso.inv_hom_id_app_assoc (MarkedPresheaf.yonedaCompExtendIso markedCylinderSite) w
    _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (markedCylinderSiteContraction.app w ≫ ·) h₂).trans (Category.comp_id _)

private theorem cylinderFaceNerveMap_comp_contraction (w : MarkedSite atomMarking) :
    cylinderFaceNerveMap w ≫ markedFaceNerve.{u}.map
        (markedExactCylinder.contraction.app ((MarkedPresheaf.yoneda atomMarking).obj w)) =
      unmarkedCompMarkedFaceNerveSiteIso.inv.app _ ≫
        markedFaceNerveSite.map (grayContractionSite w) ≫ (siteFaceNerveIso w).hom := by
  have h : cylinderBallMap w ≫ markedCylinderSiteContraction.app w =
      (MarkedPresheaf.yoneda atomMarking).map (grayContractionSite w) :=
    MarkedPresheaf.hom_ext rfl
  rw [cylinderFaceNerveMap, cylinderSiteFaceNerveMap]
  simp only [Category.assoc]
  rw [← Functor.map_comp markedFaceNerve (siteCylinderIso w).hom,
    siteCylinderIso_hom_comp_contraction,
    ← Functor.map_comp markedFaceNerve (cylinderBallMap w), h, ← siteFaceNerveIso_hom_naturality]

section Underlying

open MonoidalCategory

private theorem monotone_fst_symm_cylAtomIso (U : Atom) :
    Monotone fun z : (grayCylinder.obj U).ogp ↦ ((cylAtomIso U).inv z).1 :=
  fun _ _ h ↦ fst_symm_cylAtomIso_le h

private theorem monotone_snd_symm_cylAtomIso (U : Atom) :
    Monotone fun z : (grayCylinder.obj U).ogp ↦ ((cylAtomIso U).inv z).2 :=
  fun _ _ h ↦ ((orderIsoOfIso (cylAtomIso U)).symm.monotone h).2

private def cylChain {U : Atom} {n : SimplexCategoryᵒᵖ}
    (σ : (nerve (ULift.{u} (globe.{0} 1))).obj n) (τ : (nerve (ULift.{u} U.ogp)).obj n) :
    (nerve (ULift.{u} (grayCylinder.obj U).ogp)).obj n :=
  Monotone.functor (f := fun i ↦ ULift.up (cyl U (σ.obj i).down (τ.obj i).down))
    fun _ _ h ↦ cyl_le (ULift.down_le.2 (leOfHom (σ.map (homOfLE h))))
      (ULift.down_le.2 (leOfHom (τ.map (homOfLE h))))

private noncomputable def cylinderNerveIso (U : Atom) :
    MarkedPresheaf.forget.obj (rdcFaceNerve.obj (atomToRDCpx.obj (grayCylinder.obj U))) ≅
      (nerve (ULift.{u} (globe.{0} 1)) ⊗
        MarkedPresheaf.forget.obj (rdcFaceNerve.obj (atomToRDCpx.obj U)) : SSet.{u}) where
  hom := CartesianMonoidalCategory.lift
    (nerveMap (Monotone.functor (f := ULift.map fun z ↦ ((cylAtomIso U).inv z).1)
      fun _ _ h ↦ monotone_fst_symm_cylAtomIso U h))
    (nerveMap (Monotone.functor (f := ULift.map fun z ↦ ((cylAtomIso U).inv z).2)
      fun _ _ h ↦ monotone_snd_symm_cylAtomIso U h))
  inv :=
    { app _ := ↾fun z ↦ cylChain z.1 z.2
      naturality _ _ _ := rfl }
  hom_inv_id := by
    ext n z
    exact nerve.ext_of_isThin (C := ULift.{u} (grayCylinder.obj U).ogp)
      (funext fun _ ↦ ULift.ext _ _ (Iso.inv_hom_id_apply (cylAtomIso U) _))
  inv_hom_id := by
    ext n z
    · exact congrArg Prod.fst (Iso.hom_inv_id_apply (cylAtomIso U) _)
    · exact nerve.ext_of_isThin (C := ULift.{u} U.ogp) (funext fun _ ↦
        ULift.ext _ _ (congrArg Prod.snd (Iso.hom_inv_id_apply (cylAtomIso U) _)))

private theorem cylinderNerveIso_hom_naturality {U U' : Atom} (f : U ⟶ U') :
    MarkedPresheaf.forget.map (rdcFaceNerve.map (atomToRDCpx.map (grayCylinder.map f))) ≫
        (cylinderNerveIso U').hom =
      (cylinderNerveIso U).hom ≫
        (nerve (ULift.{u} (globe.{0} 1)) ◁ MarkedPresheaf.forget.map
          (rdcFaceNerve.map (atomToRDCpx.map f))) := by
  ext n z
  · exact congrArg Prod.fst (symm_grayCylinder_map_apply f _)
  · exact nerve.ext_of_isThin (C := ULift.{u} U'.ogp) (funext fun _ ↦
      ULift.ext _ _ (congrArg Prod.snd (symm_grayCylinder_map_apply f _)))

end Underlying

section Comparison

open MonoidalCategory

private abbrev globeNerve : SSet.{u} := nerve (ULift.{u} (globe.{0} 1))

private noncomputable def siteNerveIso (w : MarkedSite atomMarking) :
    MarkedPresheaf.forget.obj (rdcFaceNerve.{u}.obj (atomToRDCpx.obj w.obj)) ≅
      MarkedPresheaf.forget.obj (markedFaceNerve.obj ((MarkedPresheaf.yoneda atomMarking).obj w))
    where
  hom := (MarkedPresheaf.forget.map (siteFaceNerveIso w).hom :)
  inv := (MarkedPresheaf.forget.map (siteFaceNerveIso w).inv :)
  hom_inv_id := (MarkedPresheaf.forget.map_comp _ _).symm.trans
    ((congrArg MarkedPresheaf.forget.map (siteFaceNerveIso w).hom_inv_id).trans
      (MarkedPresheaf.forget.map_id _))
  inv_hom_id := (MarkedPresheaf.forget.map_comp _ _).symm.trans
    ((congrArg MarkedPresheaf.forget.map (siteFaceNerveIso w).inv_hom_id).trans
      (MarkedPresheaf.forget.map_id _))

private theorem siteNerveIso_hom_naturality {w w' : MarkedSite atomMarking} (f : w.obj ⟶ w'.obj)
    (hf : w.isMarked = true → w'.isMarked = true ∧ IsIso f ∨ atomMarking.Degenerate f) :
    MarkedPresheaf.forget.map (rdcFaceNerve.{u}.map (atomToRDCpx.map f)) ≫ (siteNerveIso w').hom =
      (siteNerveIso w).hom ≫ MarkedPresheaf.forget.map
        (markedFaceNerve.map ((MarkedPresheaf.yoneda atomMarking).map ⟨f, hf⟩)) :=
  (MarkedPresheaf.forget.map_comp _ _).symm.trans ((congrArg MarkedPresheaf.forget.map
    (siteFaceNerveIso_hom_naturality ⟨f, hf⟩)).trans (MarkedPresheaf.forget.map_comp _ _))

private noncomputable def cylinderFaceNerveSiteIso (w : MarkedSite atomMarking) :
    MarkedPresheaf.forget.obj (markedFaceNerve.{u}.obj
        (markedExactCylinder.I.obj ((MarkedPresheaf.yoneda atomMarking).obj w))) ≅
      globeNerve ⊗ MarkedPresheaf.forget.obj
        (markedFaceNerve.obj ((MarkedPresheaf.yoneda atomMarking).obj w)) :=
  (asIso (MarkedPresheaf.forget.map (cylinderFaceNerveMap w))).symm ≪≫ cylinderNerveIso w.obj ≪≫
    whiskerLeftIso globeNerve (siteNerveIso w)

private theorem cylinderFaceNerveSiteIso_hom (w : MarkedSite atomMarking) :
    (cylinderFaceNerveSiteIso.{u} w).hom =
      inv (MarkedPresheaf.forget.map (cylinderFaceNerveMap w)) ≫
        (cylinderNerveIso w.obj).hom ≫ (globeNerve ◁ (siteNerveIso w).hom) :=
  rfl

private theorem cylinderFaceNerveSiteIso_hom_naturality {w w' : MarkedSite atomMarking}
    (g : w ⟶ w') :
    MarkedPresheaf.forget.map (markedFaceNerve.{u}.map
        (markedExactCylinder.I.map ((MarkedPresheaf.yoneda atomMarking).map g))) ≫
        (cylinderFaceNerveSiteIso w').hom =
      (cylinderFaceNerveSiteIso w).hom ≫ (globeNerve ◁ MarkedPresheaf.forget.map
        (markedFaceNerve.map ((MarkedPresheaf.yoneda atomMarking).map g))) := by
  obtain ⟨f, hf⟩ := g
  have h₁ := congrArg MarkedPresheaf.forget.map (cylinderFaceNerveMap_naturality ⟨f, hf⟩)
  rw [Functor.map_comp, Functor.map_comp] at h₁
  have h₂ := siteNerveIso_hom_naturality f hf
  have h₃ := cylinderNerveIso_hom_naturality f
  refine (cancel_epi (MarkedPresheaf.forget.map (cylinderFaceNerveMap w))).1 ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (cylinderFaceNerveSiteIso w').hom) h₁).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (IsIso.hom_inv_id_assoc _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (globeNerve ◁ (siteNerveIso w').hom)) h₃).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((cylinderNerveIso w.obj).hom ≫ ·)
    (MonoidalCategory.whiskerLeft_comp _ _ _).symm).trans ?_
  refine (congrArg (fun φ ↦ (cylinderNerveIso w.obj).hom ≫ (globeNerve ◁ φ)) h₂).trans ?_
  refine (congrArg ((cylinderNerveIso w.obj).hom ≫ ·)
    (MonoidalCategory.whiskerLeft_comp _ _ _)).trans ?_
  refine Eq.trans ?_ (congrArg (MarkedPresheaf.forget.map (cylinderFaceNerveMap w) ≫ ·)
    (Category.assoc _ _ _)).symm
  refine Eq.trans ?_ (IsIso.hom_inv_id_assoc _ _).symm
  exact (Category.assoc _ _ _).symm

private noncomputable def cylinderFaceNerveForgetIso :
    markedExactCylinder.{u}.I ⋙ markedFaceNerve ⋙ MarkedPresheaf.forget ≅
      markedFaceNerve ⋙ MarkedPresheaf.forget ⋙ tensorLeft globeNerve :=
  have : PreservesColimitsOfSize.{0, u} markedExactCylinder.I :=
    inferInstanceAs (PreservesColimitsOfSize.{0, u} markedCylinder)
  MarkedPresheaf.isoOfPreservesColimits
    (NatIso.ofComponents cylinderFaceNerveSiteIso cylinderFaceNerveSiteIso_hom_naturality)

private noncomputable def globeNerveSnd :
    markedFaceNerve.{u} ⋙ MarkedPresheaf.forget ⋙ tensorLeft globeNerve ⟶
      markedFaceNerve ⋙ MarkedPresheaf.forget where
  app _ := CartesianMonoidalCategory.snd _ _
  naturality _ _ _ := CartesianMonoidalCategory.whiskerLeft_snd _ _

private theorem cylinderNerveIso_hom_comp_snd (w : MarkedSite atomMarking) :
    (cylinderNerveIso w.obj).hom ≫ CartesianMonoidalCategory.snd _ _ =
      MarkedPresheaf.forget.map (unmarkedCompMarkedFaceNerveSiteIso.inv.app _ ≫
        markedFaceNerveSite.{u}.map (grayContractionSite w)) :=
  rfl

private theorem cylinderFaceNerveForgetIso_hom_app_comp_snd (Y : MarkedDiagSet.{u}) :
    cylinderFaceNerveForgetIso.hom.app Y ≫ CartesianMonoidalCategory.snd _ _ =
      MarkedPresheaf.forget.map (markedFaceNerve.map (markedExactCylinder.contraction.app Y)) := by
  have : PreservesColimitsOfSize.{0, u} markedExactCylinder.I :=
    inferInstanceAs (PreservesColimitsOfSize.{0, u} markedCylinder)
  let β : markedExactCylinder.I ⋙ markedFaceNerve ⋙ MarkedPresheaf.forget ⟶
      markedFaceNerve ⋙ MarkedPresheaf.forget :=
    Functor.whiskerRight (Functor.whiskerRight markedExactCylinder.contraction markedFaceNerve)
      MarkedPresheaf.forget
  have h : cylinderFaceNerveForgetIso.hom ≫ globeNerveSnd = β := by
    refine MarkedPresheaf.hom_ext_of_preservesColimits (NatTrans.ext (funext fun w ↦ ?_))
    have hζ := NatTrans.congr_app (MarkedPresheaf.whiskerLeft_yoneda_isoOfPreservesColimits_hom
      (G := markedExactCylinder.{u}.I ⋙ markedFaceNerve ⋙ MarkedPresheaf.forget)
      (H := markedFaceNerve ⋙ MarkedPresheaf.forget ⋙ tensorLeft globeNerve)
      (NatIso.ofComponents cylinderFaceNerveSiteIso cylinderFaceNerveSiteIso_hom_naturality)) w
    refine (congrArg (· ≫ CartesianMonoidalCategory.snd _ _) hζ).trans ?_
    refine (cancel_epi (MarkedPresheaf.forget.map (cylinderFaceNerveMap w))).1 ?_
    refine (congrArg (MarkedPresheaf.forget.map (cylinderFaceNerveMap w) ≫ ·)
      ((congrArg (· ≫ CartesianMonoidalCategory.snd _ _) (cylinderFaceNerveSiteIso_hom w)).trans
        (Category.assoc _ _ _))).trans ?_
    refine (IsIso.hom_inv_id_assoc (MarkedPresheaf.forget.map (cylinderFaceNerveMap w)) _).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((cylinderNerveIso w.obj).hom ≫ ·)
      (CartesianMonoidalCategory.whiskerLeft_snd _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (siteNerveIso w).hom) (cylinderNerveIso_hom_comp_snd w)).trans ?_
    refine Eq.trans ?_ (MarkedPresheaf.forget.map_comp _ _)
    refine Eq.trans ?_ (congrArg MarkedPresheaf.forget.map
      (cylinderFaceNerveMap_comp_contraction w).symm)
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
    exact Category.assoc _ _ _
  exact NatTrans.congr_app h Y

end Comparison

private theorem grayCylinder_map_apply_cyl {V U : Atom} (f : V ⟶ U)
    (a : globe.{0} 1) (x : V.ogp) :
    grayCylinder.map f (cyl V a x) = cyl U a (f x) := by
  have h := symm_grayCylinder_map_apply f (cyl V a x)
  rw [Iso.hom_inv_id_apply] at h
  exact (Iso.inv_hom_id_apply (cylAtomIso U) _).symm.trans (congrArg (cylAtomIso U).hom h)

private theorem forget_map_rdcFaceNerve_map_app_nerveEdge {V U : Atom} (f : V ⟶ U)
    {x y : V.ogp} (h : x ≤ y) :
    (MarkedPresheaf.forget.map (rdcFaceNerve.{u}.map (atomToRDCpx.map f))).app _ (nerveEdge h) =
      nerveEdge ((Atom.isMap f).monotone h) :=
  nerve.ext_of_isThin (funext fun i ↦ by fin_cases i <;> rfl)

private theorem cylinderFaceNerveMap_mem_marked_of_outV_eq (w : MarkedSite atomMarking)
    {z z' : (grayCylinder.obj w.obj).ogp} (h : z ≤ z')
    (hz : outV _ z = outV _ z') :
    (MarkedPresheaf.forget.map (cylinderFaceNerveMap w)).app _ (nerveEdge h) ∈
      (markedFaceNerve.{u}.obj (markedExactCylinder.I.obj
        ((MarkedPresheaf.yoneda atomMarking).obj w))).marked ⦋1⦌ :=
  MarkedPresheaf.map_mem_marked (cylinderFaceNerveMap w)
    ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 ⟨rfl, Or.inl hz⟩)

private theorem cylinderFaceNerveMap_mem_marked_vertex (w : MarkedSite atomMarking)
    {v : w.obj.ogp} (hv : grade ℕ v = 0) :
    (MarkedPresheaf.forget.map (cylinderFaceNerveMap w)).app _
        (nerveEdge (cyl_le (le_gEdge (gIn false)) (le_refl v))) ∈
      (markedFaceNerve.{u}.obj (markedExactCylinder.I.obj
        ((MarkedPresheaf.yoneda atomMarking).obj w))).marked ⦋1⦌ := by
  let V := grayCylinder.obj (Atom.ofClosure w.obj v)
  let c := grayCylinder.map (Atom.closureIncl w.obj v)
  have hV₁ : V.dimension = 1 := by
    rw [dimension_grayCylinder_obj, Atom.dimension_ofClosure, hv]
  have hV : atomMarking.markable V := by
    change 0 < V.dimension
    rw [hV₁]
    exact Nat.one_pos
  have hc : c V.top ∈ cylinderMarked w := by
    refine Or.inl ?_
    rw [symm_grayCylinder_map_apply, symm_cylAtomIso_top]
  have hm := cylinderSiteFaceNerveMap_mem_marked w hV hV₁ c hc
    (cyl (Atom.ofClosure w.obj v) (gIn false) (Atom.ofClosure w.obj v).top)
  have he : (MarkedPresheaf.forget.map (rdcFaceNerve.map (atomToRDCpx.map c))).app _
      (nerveEdge (V.le_top (cyl (Atom.ofClosure w.obj v) (gIn false)
        (Atom.ofClosure w.obj v).top))) =
      nerveEdge (cyl_le (le_gEdge (gIn false)) (le_refl v)) := by
    refine (forget_map_rdcFaceNerve_map_app_nerveEdge c _).trans
      (nerve.ext_of_isThin (funext fun i ↦ ?_))
    fin_cases i
    · exact congrArg ULift.up ((grayCylinder_map_apply_cyl _ _ _).trans
        (congrArg (cyl w.obj (gIn false)) (Atom.closureIncl_top w.obj v)))
    · exact congrArg ULift.up ((congrArg c (cylAtomIso_top_top _)).symm.trans
        ((grayCylinder_map_apply_cyl _ _ _).trans
          (congrArg (cyl w.obj gEdge) (Atom.closureIncl_top w.obj v))))
  have hm' := MarkedPresheaf.map_mem_marked (markedFaceNerve.map (siteCylinderIso w).hom) hm
  refine (congrArg (· ∈ _) ?_).mp hm'
  exact congrArg ((MarkedPresheaf.forget.map (markedFaceNerve.map (siteCylinderIso w).hom)).app _)
    (congrArg ((MarkedPresheaf.forget.map (cylinderSiteFaceNerveMap w)).app _) he)

private theorem grayEndpoint_app_apply (ε : Bool) (U : Atom) (x : U.ogp) :
    (grayEndpoint ε).app U x = cyl U (gIn ε) x :=
  (Iso.inv_hom_id_apply (cylAtomIso U) _).symm.trans
    (congrArg (cylAtomIso U).hom (symm_grayEndpoint_apply ε U x))

private theorem cylinderFaceNerveMap_mem_marked_endpoint (w : MarkedSite atomMarking)
    (hw : w.isMarked = true) (h₁ : w.obj.dimension = 1) (ε : Bool) (x : w.obj.ogp) :
    (MarkedPresheaf.forget.map (cylinderFaceNerveMap w)).app _
        (nerveEdge (cyl_le (le_refl (gIn ε)) (w.obj.le_top x))) ∈
      (markedFaceNerve.{u}.obj (markedExactCylinder.I.obj
        ((MarkedPresheaf.yoneda atomMarking).obj w))).marked ⦋1⦌ := by
  let c := (grayEndpoint ε).app w.obj
  have hV : atomMarking.markable w.obj := by
    change 0 < w.obj.dimension
    rw [h₁]
    exact Nat.one_pos
  have hc : c w.obj.top ∈ cylinderMarked w :=
    Or.inr ⟨hw, congrArg Prod.snd (symm_grayEndpoint_apply ε w.obj w.obj.top)⟩
  have hm := cylinderSiteFaceNerveMap_mem_marked w hV h₁ c hc x
  have he : (MarkedPresheaf.forget.map (rdcFaceNerve.map (atomToRDCpx.map c))).app _
      (nerveEdge (w.obj.le_top x)) = nerveEdge (cyl_le (le_refl (gIn ε)) (w.obj.le_top x)) := by
    refine (forget_map_rdcFaceNerve_map_app_nerveEdge c _).trans
      (nerve.ext_of_isThin (funext fun i ↦ ?_))
    fin_cases i
    · exact congrArg ULift.up (grayEndpoint_app_apply ε w.obj x)
    · exact congrArg ULift.up (grayEndpoint_app_apply ε w.obj w.obj.top)
  have hm' := MarkedPresheaf.map_mem_marked (markedFaceNerve.map (siteCylinderIso w).hom) hm
  refine (congrArg (· ∈ _) ?_).mp hm'
  exact congrArg ((MarkedPresheaf.forget.map (markedFaceNerve.map (siteCylinderIso w).hom)).app _)
    (congrArg ((MarkedPresheaf.forget.map (cylinderSiteFaceNerveMap w)).app _) he)

section Contraction

open MonoidalCategory MarkedSSet.modelCategoryCartesian

private noncomputable def cylinderFaceNerveProd (Y : MarkedDiagSet.{u}) :
    markedFaceNerve.obj (markedExactCylinder.I.obj Y) ⟶
      sharpProdObj globeNerve (markedFaceNerve.obj Y) :=
  edgeHomMk (Y := sharpProdObj globeNerve (markedFaceNerve.obj Y))
    (cylinderFaceNerveForgetIso.hom.app Y) fun e he ↦ (mem_marked_sharpProdObj _ _ _).2 (by
      have hm := MarkedPresheaf.map_mem_marked
        (markedFaceNerve.map (markedExactCylinder.contraction.app Y)) he
      refine (congrArg (· ∈ (markedFaceNerve.obj Y).marked ⦋1⦌) ?_).mp hm
      exact (ConcreteCategory.congr_hom (NatTrans.congr_app
        (cylinderFaceNerveForgetIso_hom_app_comp_snd Y) _) e).symm)

private theorem cylinderFaceNerveProd_comp_sharpProdProj (Y : MarkedDiagSet.{u}) :
    cylinderFaceNerveProd Y ≫ sharpProdProj globeNerve (markedFaceNerve.obj Y) =
      markedFaceNerve.map (markedExactCylinder.contraction.app Y) :=
  MarkedPresheaf.hom_ext ((MarkedPresheaf.forget.map_comp _ _).trans
    (cylinderFaceNerveForgetIso_hom_app_comp_snd Y))

private theorem exists_mem_marked_markedFaceNerve_eq {Y : MarkedDiagSet.{u}}
    {e : (markedFaceNerve.obj Y).underlying _⦋1⦌} (he : e ∈ (markedFaceNerve.obj Y).marked ⦋1⦌) :
    ∃ (w : MarkedSite atomMarking) (c : (MarkedPresheaf.yoneda atomMarking).obj w ⟶ Y)
      (e' : (markedFaceNerveSite.obj w).underlying _⦋1⦌),
        e' ∈ (markedFaceNerveSite.obj w).marked ⦋1⦌ ∧
          (MarkedPresheaf.forget.map ((siteFaceNerveIso w).hom ≫ markedFaceNerve.map c)).app _ e' =
            e := by
  have hc := isColimitOfPreserves markedFaceNerve ((MarkedPresheaf.yoneda atomMarking).denseAt Y)
  have key : ∀ (w : MarkedSite atomMarking) (c : (MarkedPresheaf.yoneda atomMarking).obj w ⟶ Y)
      (x : (markedFaceNerve.obj ((MarkedPresheaf.yoneda atomMarking).obj w)).underlying _⦋1⦌),
      x ∈ (markedFaceNerve.obj ((MarkedPresheaf.yoneda atomMarking).obj w)).marked ⦋1⦌ →
        (MarkedPresheaf.forget.map (markedFaceNerve.map c)).app _ x = e →
        ∃ (w : MarkedSite atomMarking) (c : (MarkedPresheaf.yoneda atomMarking).obj w ⟶ Y)
          (e' : (markedFaceNerveSite.obj w).underlying _⦋1⦌),
            e' ∈ (markedFaceNerveSite.obj w).marked ⦋1⦌ ∧
              (MarkedPresheaf.forget.map ((siteFaceNerveIso w).hom ≫
                markedFaceNerve.map c)).app _ e' = e := by
    intro w c x hx hxe
    refine ⟨w, c, (MarkedPresheaf.forget.map (siteFaceNerveIso w).inv).app _ x,
      MarkedPresheaf.map_mem_marked _ hx, Eq.trans ?_ hxe⟩
    exact congrArg (fun φ ↦ (MarkedPresheaf.forget.map φ).app _ x)
      ((siteFaceNerveIso w).inv_hom_id_assoc (markedFaceNerve.map c))
  rcases exists_mem_marked_of_isColimit hc he with ⟨j, x, hx, hxe⟩ | ⟨v, hv⟩
  · exact key j.left _ x hx hxe
  · obtain ⟨j, v', hv'⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves ((evaluation _ _).obj _)
        (isColimitOfPreserves MarkedPresheaf.forget hc)) v
    refine key j.left (((Functor.LeftExtension.mk (𝟭 (MarkedPresheaf atomMarking))
      (MarkedPresheaf.yoneda atomMarking).rightUnitor.inv).coconeAt Y).ι.app j) _
      (MarkedSSet.map_σ_mem_marked _ v') ?_
    exact (SSet.σ_naturality_apply (MarkedPresheaf.forget.map (markedFaceNerve.map _)) 0 v').trans
      ((congrArg _ hv').trans hv)

private theorem cylinderFaceNerveMap_comp_forgetIso_hom_app {Y : MarkedDiagSet.{u}}
    (w : MarkedSite atomMarking) (c : (MarkedPresheaf.yoneda atomMarking).obj w ⟶ Y) :
    MarkedPresheaf.forget.map (cylinderFaceNerveMap w) ≫
        MarkedPresheaf.forget.map (markedFaceNerve.map (markedExactCylinder.I.map c)) ≫
          cylinderFaceNerveForgetIso.hom.app Y =
      (cylinderNerveIso w.obj).hom ≫
        (globeNerve ◁ ((siteNerveIso w).hom ≫
          MarkedPresheaf.forget.map (markedFaceNerve.map c))) := by
  have : PreservesColimitsOfSize.{0, u} markedExactCylinder.I :=
    inferInstanceAs (PreservesColimitsOfSize.{0, u} markedCylinder)
  have hζ := NatTrans.congr_app (MarkedPresheaf.whiskerLeft_yoneda_isoOfPreservesColimits_hom
    (G := markedExactCylinder.{u}.I ⋙ markedFaceNerve ⋙ MarkedPresheaf.forget)
    (H := markedFaceNerve ⋙ MarkedPresheaf.forget ⋙ tensorLeft globeNerve)
    (NatIso.ofComponents cylinderFaceNerveSiteIso cylinderFaceNerveSiteIso_hom_naturality)) w
  refine (congrArg (MarkedPresheaf.forget.map (cylinderFaceNerveMap w) ≫ ·)
    (cylinderFaceNerveForgetIso.hom.naturality c)).trans ?_
  refine (congrArg (fun φ ↦ MarkedPresheaf.forget.map (cylinderFaceNerveMap w) ≫ φ ≫
    (globeNerve ◁ MarkedPresheaf.forget.map (markedFaceNerve.map c))) hζ).trans ?_
  refine (congrArg (MarkedPresheaf.forget.map (cylinderFaceNerveMap w) ≫ ·)
    ((congrArg (· ≫ (globeNerve ◁ MarkedPresheaf.forget.map (markedFaceNerve.map c)))
      (cylinderFaceNerveSiteIso_hom w)).trans (Category.assoc _ _ _))).trans ?_
  refine (IsIso.hom_inv_id_assoc (MarkedPresheaf.forget.map (cylinderFaceNerveMap w)) _).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg ((cylinderNerveIso w.obj).hom ≫ ·)
    (MonoidalCategory.whiskerLeft_comp _ _ _).symm)

private theorem weakEquivalence_cylinderFaceNerveProd (Y : MarkedDiagSet.{u}) :
    WeakEquivalence (cylinderFaceNerveProd Y) := by
  have : IsIso (MarkedPresheaf.forget.map (cylinderFaceNerveProd Y)) :=
    inferInstanceAs (IsIso (cylinderFaceNerveForgetIso.hom.app Y))
  refine weakEquivalence_of_isIso_forget_map _ fun F _ g hg e he ↦ ?_
  obtain ⟨w, c, e', he', hee⟩ :=
    exists_mem_marked_markedFaceNerve_eq ((mem_marked_sharpProdObj _ _ e).1 he)
  let h := MarkedPresheaf.forget.map (cylinderFaceNerveMap w) ≫
    MarkedPresheaf.forget.map (markedFaceNerve.map (markedExactCylinder.I.map c)) ≫
      MarkedPresheaf.forget.map (cylinderFaceNerveProd Y) ≫ g
  have hinv {z z' : (grayCylinder.obj w.obj).ogp} (hz : z ≤ z')
      (hm : (MarkedPresheaf.forget.map (cylinderFaceNerveMap w)).app _ (nerveEdge hz) ∈
        (markedFaceNerve.obj (markedExactCylinder.I.obj
          ((MarkedPresheaf.yoneda atomMarking).obj w))).marked ⦋1⦌) : NerveInv h hz :=
    hg _ (MarkedPresheaf.map_mem_marked (markedFaceNerve.map (markedExactCylinder.I.map c)) hm)
  obtain ⟨-, hm⟩ := (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 he'
  have key := nerveInv_cyl h {y | w.isMarked = true ∧ IsMax y}
    (fun _ _ hz hout ↦ hinv hz (cylinderFaceNerveMap_mem_marked_of_outV_eq w hz hout))
    (fun _ hv ↦ hinv _ (cylinderFaceNerveMap_mem_marked_vertex w hv))
    (fun y hy hd ε x hx ↦ by
      obtain rfl : y = w.obj.top := le_antisymm (w.obj.le_top y) (hy.2 (w.obj.le_top y))
      exact hinv _ (cylinderFaceNerveMap_mem_marked_endpoint w hy.1
        (w.obj.dimension_eq.trans hd) ε x))
    (ULift.down_le.2 (leOfHom e.1.hom)) (ULift.down_le.2 (leOfHom e'.hom)) hm
  have hz : (cylinderNerveIso w.obj).inv.app _ (e.1, e') =
      nerveEdge (cyl_le (ULift.down_le.2 (leOfHom e.1.hom)) (ULift.down_le.2 (leOfHom e'.hom))) :=
    nerve.ext_of_isThin (funext fun i ↦ by fin_cases i <;> rfl)
  have hval : h.app _ (nerveEdge (cyl_le (ULift.down_le.2 (leOfHom e.1.hom))
      (ULift.down_le.2 (leOfHom e'.hom)))) = g.app _ e := by
    refine (congrArg (h.app _) hz.symm).trans ?_
    have hc := cylinderFaceNerveMap_comp_forgetIso_hom_app w c
    refine congrArg (g.app _) ((ConcreteCategory.congr_hom (NatTrans.congr_app hc _) _).trans ?_)
    refine (congrArg ((globeNerve ◁ ((siteNerveIso w).hom ≫
      MarkedPresheaf.forget.map (markedFaceNerve.map c))).app _)
      (Iso.inv_hom_id_app_apply (cylinderNerveIso w.obj) _ _)).trans ?_
    exact Prod.ext rfl hee
  exact (congrArg (fun t ↦ Nonempty (SSet.Edge.mk' t).InvStruct) hval).mp key

theorem weakEquivalence_markedFaceNerve_map_contraction_app (Y : MarkedDiagSet.{u}) :
    WeakEquivalence (markedFaceNerve.map (markedExactCylinder.contraction.app Y)) := by
  rw [← cylinderFaceNerveProd_comp_sharpProdProj]
  exact (weakEquivalence_iff _).2 ((weakEquivalences MarkedSSet).comp_mem _ _
    ((weakEquivalence_iff _).1 (weakEquivalence_cylinderFaceNerveProd Y))
    ((weakEquivalence_iff _).1 (weakEquivalence_of_sharpEdgeHomotopy _ _
      (sharpProdIncl_comp_sharpProdProj gEdgeVertex (markedFaceNerve.obj Y))
      (sharpProdContraction _) (sharpEdgeEndpoint_zero_app_comp_sharpProdContraction _)
      (sharpEdgeEndpoint_one_app_comp_sharpProdContraction _))))

end Contraction

end Atoms.Diagrammatic

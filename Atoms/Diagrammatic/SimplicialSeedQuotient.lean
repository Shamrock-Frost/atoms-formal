import Atoms.Diagrammatic.HomotopyCategory
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Atoms.ForMathlib.CategoryTheory.Comma.Arrow

open CategoryTheory Simplicial Opposite
open Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X Y Z : DiagSet.{u}}

namespace SimplicialSeedQuotient
scoped macro "tr₂[" X:term "]" : term =>
  `((SSet.truncation 2).obj (DiagSet.toSSet.obj $X))

scoped macro "hmap[" f:term "]" : term =>
  `(SSet.Truncated.mapHomotopyCategory ((SSet.truncation 2).map (DiagSet.toSSet.map $f)))

end SimplicialSeedQuotient

open scoped SimplicialSeedQuotient

namespace SimplicialSeedQuotient

inductive IsComposite : PastingDiagram X → {x y : (DiagSet.toSSet.obj X) _⦋0⦌} →
    (SSet.Truncated.HomotopyCategory.mk (V := tr₂[X]) x ⟶
      SSet.Truncated.HomotopyCategory.mk y) → Prop
  | edge {x y : (DiagSet.toSSet.obj X) _⦋0⦌} (e : SSet.Edge x y) :
      IsComposite (ofCell (e.edge : diagram X (atomSimplex 1)))
        (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)
  | paste {u v : PastingDiagram X} (h : u.Pastable v 0) {x y z : (DiagSet.toSSet.obj X) _⦋0⦌}
      {φ : SSet.Truncated.HomotopyCategory.mk (V := tr₂[X]) x ⟶
        SSet.Truncated.HomotopyCategory.mk y}
      {ψ : SSet.Truncated.HomotopyCategory.mk (V := tr₂[X]) y ⟶
        SSet.Truncated.HomotopyCategory.mk z} :
      IsComposite u φ → IsComposite v ψ → IsComposite (u.paste v 0 h) (φ ≫ ψ)
  | equiv {u v : PastingDiagram X} (h : u.Equiv v) {x y : (DiagSet.toSSet.obj X) _⦋0⦌}
      {φ : SSet.Truncated.HomotopyCategory.mk (V := tr₂[X]) x ⟶
        SSet.Truncated.HomotopyCategory.mk y} :
      IsComposite u φ → IsComposite v φ

theorem IsComposite.map (f : X ⟶ Y) {u : PastingDiagram X} {x y : (DiagSet.toSSet.obj X) _⦋0⦌}
    {φ : SSet.Truncated.HomotopyCategory.mk (V := tr₂[X]) x ⟶
      SSet.Truncated.HomotopyCategory.mk y}
    (h : IsComposite u φ) : IsComposite (u.mapTo f) ((hmap[f]).map φ) := by
  induction h with
  | edge e =>
    have h : ofCell ((e.map (DiagSet.toSSet.map f)).edge : diagram Y (atomSimplex 1)) =
        (ofCell (e.edge : diagram X (atomSimplex 1))).mapTo f :=
      PastingDiagram.ofCell_app f _
    exact h ▸ IsComposite.edge (e.map (DiagSet.toSSet.map f))
  | paste h _ _ hu hv =>
    rw [Functor.map_comp]
    exact IsComposite.equiv (paste_mapTo _ _ 0 h f (h.mapTo f)).symm
      (IsComposite.paste (h.mapTo f) hu hv)
  | equiv h _ hu => exact IsComposite.equiv (h.mapTo f) hu

open Atoms.Molecule Atoms.Molecule.OGP Order in
theorem IsComposite.hasBdry {u : PastingDiagram X} {x y : (DiagSet.toSSet.obj X) _⦋0⦌}
    {φ : SSet.Truncated.HomotopyCategory.mk (V := tr₂[X]) x ⟶
      SSet.Truncated.HomotopyCategory.mk y}
    (h : IsComposite u φ) :
    HasBdry false 0 u (PastingDiagram.ofCell (x : diagram X (atomSimplex 0)))
      (PastingDiagram.ofCell (y : diagram X (atomSimplex 0))) := by
  induction h with
  | edge e => exact hasBdry_ofCell_simplexEdge e
  | paste hp _ _ hu hv =>
    refine ⟨?_, hu.dim_a, hv.dim_b, (equiv_boundary_paste hp false).trans hu.side,
      (equiv_boundary_paste hp true).trans hv.other⟩
    rw [dim_paste, hu.dim_h, hv.dim_h, max_self]
  | equiv he _ hu =>
    exact ⟨(dim_eq_of_equiv he).symm.trans hu.dim_h, hu.dim_a, hu.dim_b,
      (he.boundary 0 false).symm.trans hu.side, (he.boundary 0 true).symm.trans hu.other⟩

inductive Rel (X : DiagSet.{u}) :
    HomRel (SSet.Truncated.HomotopyCategory tr₂[X])
  | boundary {V : Atom} (hV : V.dimension = 2) (c : diagram X V)
      {x y : (DiagSet.toSSet.obj (ball.{u} V)) _⦋0⦌}
      {φ ψ : SSet.Truncated.HomotopyCategory.mk (V := tr₂[ball.{u} V]) x ⟶
        SSet.Truncated.HomotopyCategory.mk y}
      (hφ : IsComposite
        ((PastingDiagram.ofCell (uliftYonedaEquiv (𝟙 (ball.{u} V)))).boundary 1 false) φ)
      (hψ : IsComposite
        ((PastingDiagram.ofCell (uliftYonedaEquiv (𝟙 (ball.{u} V)))).boundary 1 true) ψ) :
      Rel X ((hmap[uliftYonedaEquiv.symm c]).map φ)
        ((hmap[uliftYonedaEquiv.symm c]).map ψ)

end SimplicialSeedQuotient

abbrev SimplicialSeedQuotient (X : DiagSet.{u}) : Type u :=
  CategoryTheory.Quotient (SimplicialSeedQuotient.Rel X)

instance : Category (SimplicialSeedQuotient X) :=
  inferInstanceAs (Category (CategoryTheory.Quotient (SimplicialSeedQuotient.Rel X)))

namespace SimplicialSeedQuotient

def quotientFunctor (X : DiagSet.{u}) :
    SSet.Truncated.HomotopyCategory tr₂[X] ⥤ SimplicialSeedQuotient X :=
  CategoryTheory.Quotient.functor _

instance : (quotientFunctor X).Full :=
  CategoryTheory.Quotient.full_functor _

def mk (x : (DiagSet.toSSet.obj X) _⦋0⦌) : SimplicialSeedQuotient X :=
  (quotientFunctor X).obj (SSet.Truncated.HomotopyCategory.mk x)

def homMk {x y : (DiagSet.toSSet.obj X) _⦋0⦌} (e : SSet.Edge x y) : mk x ⟶ mk y :=
  (quotientFunctor X).map (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)
section Lift

variable {D : Type*} [Category* D] (F : SSet.Truncated.HomotopyCategory tr₂[X] ⥤ D)
  (hF : ∀ (a b : SSet.Truncated.HomotopyCategory tr₂[X]) (φ ψ : a ⟶ b), Rel X φ ψ →
    F.map φ = F.map ψ)

def lift : SimplicialSeedQuotient X ⥤ D :=
  CategoryTheory.Quotient.lift _ F hF

theorem quotientFunctor_comp_lift : quotientFunctor X ⋙ lift F hF = F :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp]
theorem lift_obj_mk (x : (DiagSet.toSSet.obj X) _⦋0⦌) :
    (lift F hF).obj (mk x) = F.obj (SSet.Truncated.HomotopyCategory.mk x) :=
  rfl

@[simp]
theorem lift_map_homMk {x y : (DiagSet.toSSet.obj X) _⦋0⦌} (e : SSet.Edge x y) :
    (lift F hF).map (homMk e) = F.map (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) :=
  CategoryTheory.Quotient.lift_map_functor_map _ _ _ _

end Lift

theorem functor_ext {D : Type*} [Category* D] {F G : SimplicialSeedQuotient X ⥤ D}
    (h : ∀ ⦃x y : (DiagSet.toSSet.obj X) _⦋0⦌⦄ (e : SSet.Edge x y),
      Arrow.mk (F.map (homMk e)) = Arrow.mk (G.map (homMk e))) : F = G :=
  CategoryTheory.Quotient.lift_unique' _ _ _
    (SSet.Truncated.HomotopyCategory.functor_ext_of_arrowMk h)

private theorem hmap_comp (f : X ⟶ Y) (g : Y ⟶ Z) : hmap[f ≫ g] = hmap[f] ⋙ hmap[g] :=
  congrArg Cat.Hom.toFunctor ((DiagSet.toSSet ⋙ SSet.hoFunctor).map_comp f g)

private theorem hmap_id (X : DiagSet.{u}) :
    hmap[𝟙 X] = 𝟭 (SSet.Truncated.HomotopyCategory tr₂[X]) :=
  congrArg Cat.Hom.toFunctor ((DiagSet.toSSet ⋙ SSet.hoFunctor).map_id X)

private theorem map_eq_map_of_rel (f : X ⟶ Y) {a b : SSet.Truncated.HomotopyCategory tr₂[X]}
    (φ ψ : a ⟶ b) (h : Rel X φ ψ) :
    (hmap[f] ⋙ quotientFunctor Y).map φ =
      (hmap[f] ⋙ quotientFunctor Y).map ψ := by
  induction h with
  | boundary hV c hφ hψ =>
    have h : hmap[uliftYonedaEquiv.symm c] ⋙ hmap[f] =
        hmap[uliftYonedaEquiv.symm (f.app _ c)] := by
      rw [← hmap_comp, uliftYonedaEquiv_symm_comp]
    have e := CategoryTheory.Quotient.sound _ (Rel.boundary hV (f.app _ c) hφ hψ)
    change (quotientFunctor Y).map ((hmap[uliftYonedaEquiv.symm c] ⋙ hmap[f]).map _) =
      (quotientFunctor Y).map ((hmap[uliftYonedaEquiv.symm c] ⋙ hmap[f]).map _)
    rw [Functor.congr_hom h, Functor.congr_hom h, Functor.map_comp, Functor.map_comp,
      Functor.map_comp, Functor.map_comp]
    exact congrArg (_ ≫ · ≫ _) e

def map (f : X ⟶ Y) : SimplicialSeedQuotient X ⥤ SimplicialSeedQuotient Y :=
  lift (hmap[f] ⋙ quotientFunctor Y) fun _ _ => map_eq_map_of_rel f

theorem map_map_homMk (f : X ⟶ Y) {x y : (DiagSet.toSSet.obj X) _⦋0⦌} (e : SSet.Edge x y) :
    (map f).map (homMk e) = homMk (e.map (DiagSet.toSSet.map f)) :=
  lift_map_homMk _ (fun _ _ => map_eq_map_of_rel f) e

theorem quotientFunctor_comp_map (f : X ⟶ Y) :
    quotientFunctor X ⋙ map f = hmap[f] ⋙ quotientFunctor Y :=
  quotientFunctor_comp_lift _ fun _ _ => map_eq_map_of_rel f

private theorem exists_edge_of_isComposite (hX : IsInftyCategory 1 X) {u : PastingDiagram X}
    {x y : (DiagSet.toSSet.obj X) _⦋0⦌}
    {φ : SSet.Truncated.HomotopyCategory.mk (V := tr₂[X]) x ⟶
      SSet.Truncated.HomotopyCategory.mk y}
    (h : IsComposite u φ) :
    ∃ (hr : u.IsRound) (e : X.Edge (X.vertexEquivSSet.symm x) (X.vertexEquivSSet.symm y)),
      Equivalent ⟨u, hr⟩ (cellRound e.cell) ∧
        (homotopyCategoryEquivalence hX).inverse.map φ = HomotopyCategory.homMk hX.1 e := by
  induction h with
  | edge e =>
    exact ⟨(cellRound (e.edge : diagram X (atomSimplex 1))).isRound, X.edgeEquivSSet.symm e,
      equivalent_of_equiv (equiv_ofCell_edgeEquivSSet_symm e),
      homotopyCategoryEquivalence_inverse_map_homMk hX e⟩
  | @paste u v hp x y z φ ψ _ _ hu hv =>
    obtain ⟨hru, f, hf, hφ⟩ := hu
    obtain ⟨hrv, g, hg, hψ⟩ := hv
    have hud : u.dim = 1 := hf.data.dim_eq.trans (dimension_atomGlobe 1)
    have hvd : v.dim = 1 := hg.data.dim_eq.trans (dimension_atomGlobe 1)
    have hr := isRound_paste_of_dim ⟨u, hru⟩ ⟨v, hrv⟩ hud hvd hp
    have hp' := pastable_of_equivalent_left (v := ⟨v, hrv⟩) hf hp
    have hr' := isRound_paste_of_dim (cellRound f.cell) ⟨v, hrv⟩ (dimension_atomGlobe 1) hvd hp'
    obtain ⟨k, hk⟩ := exists_edge_equivalent_pasteEdges hX.1 f g
    refine ⟨hr, k, equivalent_trans (equivalent_trans
      (equivalent_paste_left (v := ⟨v, hrv⟩) hf (hud.trans hvd.symm) hp hp' hr hr')
      (equivalent_paste_right (u := cellRound f.cell) hg rfl
        ((dimension_atomGlobe 1).trans hvd.symm) hp' (pastable_ofCell_edge f g) hr'
        (pasteEdges f g).isRound)) hk, ?_⟩
    refine ((homotopyCategoryEquivalence hX).inverse.map_comp φ ψ).trans ?_
    rw [hφ, hψ]
    exact (HomotopyCategory.homMk_comp_homMk_iff hX.1 f g k).2 hk
  | @equiv u v he x y φ _ hu =>
    obtain ⟨hru, f, hf, hφ⟩ := hu
    have hrv := he.isRound_iff.1 hru
    exact ⟨hrv, f, equivalent_trans (equivalent_of_equiv (u := ⟨v, hrv⟩) (v := ⟨u, hru⟩) he.symm)
      hf, hφ⟩

private theorem inverse_map_eq_of_rel (hX : IsInftyCategory 1 X)
    {a b : SSet.Truncated.HomotopyCategory tr₂[X]} (φ ψ : a ⟶ b) (h : Rel X φ ψ) :
    (homotopyCategoryEquivalence hX).inverse.map φ =
      (homotopyCategoryEquivalence hX).inverse.map ψ := by
  induction h with
  | @boundary V hV c x y φ ψ hφ hψ =>
    obtain ⟨hr₁, f, hf, e₁⟩ := exists_edge_of_isComposite hX (hφ.map (uliftYonedaEquiv.symm c))
    obtain ⟨hr₂, g, hg, e₂⟩ := exists_edge_of_isComposite hX (hψ.map (uliftYonedaEquiv.symm c))
    have hd : (ofCell c).dim = 1 + 1 := hV
    have hb : ∀ α, ((ofCell c).boundary 1 α).dim = 1 := fun α =>
      (ofCell c).dim_boundary (by rw [hd]; exact Nat.le_succ 1) α
    have hr : ∀ α, ((ofCell c).boundary 1 α).IsRound := fun α =>
      isRound_boundary_of_isRound (cellRound c).isRound 1 α
    have h₁ : (⟨_, hr₁⟩ : RoundPastingDiagram X) = ⟨_, hr false⟩ :=
      RoundPastingDiagram.ext (boundary_ofCell_taut_mapTo c 1 false)
    have h₂ : (⟨_, hr₂⟩ : RoundPastingDiagram X) = ⟨_, hr true⟩ :=
      RoundPastingDiagram.ext (boundary_ofCell_taut_mapTo c 1 true)
    rw [h₁] at hf
    rw [h₂] at hg
    have hs : cellRound c ∈ equivalences X :=
      hX.2 V c (by rw [hV]; exact_mod_cast (by omega : 1 < 2))
    have E := equivalent_of_mem_equivalences_cond false hs (u := ⟨_, hr false⟩)
      (v := ⟨_, hr true⟩) (hb false) (hb true) hd (.refl _) (.refl _)
    exact e₁.trans (((HomotopyCategory.homMk_eq_homMk_iff hX.1 f g).2
      (equivalent_trans (equivalent_symm hf) (equivalent_trans E hg))).trans e₂.symm)

noncomputable def toHomotopyCategory (hX : IsInftyCategory 1 X) :
    SimplicialSeedQuotient X ⥤ HomotopyCategory X hX.1 :=
  lift (homotopyCategoryEquivalence hX).inverse fun _ _ =>
    inverse_map_eq_of_rel hX

theorem toHomotopyCategory_map_homMk (hX : IsInftyCategory 1 X)
    {x y : X.Vertex} (e : SSet.Edge (X.vertexEquivSSet x) (X.vertexEquivSSet y)) :
    (toHomotopyCategory hX).map (homMk e) =
      HomotopyCategory.homMk hX.1 (X.edgeEquivSSet.symm e) :=
  (lift_map_homMk _ (fun _ _ => inverse_map_eq_of_rel hX) e).trans
    (homotopyCategoryEquivalence_inverse_map_homMk hX e)

private theorem quotientFunctor_comp_toHomotopyCategory (hX : IsInftyCategory 1 X) :
    quotientFunctor X ⋙ toHomotopyCategory hX =
      (homotopyCategoryEquivalence hX).inverse :=
  quotientFunctor_comp_lift _ _

theorem isEquivalence_quotientFunctor (hX : IsInftyCategory 1 X) :
    (quotientFunctor X).IsEquivalence := by
  have hfaith : (quotientFunctor X).Faithful := by
    refine ⟨fun {a b} φ ψ h => (homotopyCategoryEquivalence hX).inverse.map_injective ?_⟩
    rw [← quotientFunctor_comp_toHomotopyCategory hX, Functor.comp_map, Functor.comp_map, h]
  have hess : (quotientFunctor X).EssSurj :=
    inferInstanceAs (CategoryTheory.Quotient.functor (Rel X)).EssSurj
  exact { faithful := hfaith, full := inferInstance, essSurj := hess }

theorem isEquivalence_toHomotopyCategory (hX : IsInftyCategory 1 X) :
    (toHomotopyCategory hX).IsEquivalence := by
  have := isEquivalence_quotientFunctor hX
  have : (quotientFunctor X ⋙ toHomotopyCategory hX).IsEquivalence := by
    rw [quotientFunctor_comp_toHomotopyCategory hX]
    exact (homotopyCategoryEquivalence hX).isEquivalence_inverse
  exact Functor.isEquivalence_of_comp_left (quotientFunctor X) _

end SimplicialSeedQuotient

end Atoms.Diagrammatic

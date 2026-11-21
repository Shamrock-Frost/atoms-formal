import Atoms.Diagrammatic.Context.RoundBicategoryEquivalence
import Atoms.ForMathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Atoms.ForMathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Bicategory Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X Y Z : DiagSet.{u}} {n : ℕ}

namespace RoundBicat

def mapObj (φ : X ⟶ Y) (a : RoundBicat X n) : RoundBicat Y n :=
  ⟨a.diag.mapTo φ, a.dim_diag⟩

def Arrow.mapTo (φ : X ⟶ Y) {a b : RoundBicat X n} (p : Arrow a b) :
    Arrow (mapObj φ a) (mapObj φ b) :=
  ⟨p.diag.mapTo φ, ⟨p.hasBdry.dim_h, p.hasBdry.dim_a, p.hasBdry.dim_b,
    p.hasBdry.side.mapTo_boundary φ, p.hasBdry.other.mapTo_boundary φ⟩⟩

def mapHom (φ : X ⟶ Y) {a b : RoundBicat X n} (f : a ⟶ b) : mapObj φ a ⟶ mapObj φ b :=
  Quotient.map (Arrow.mapTo φ) (fun _ _ h => PastingDiagram.Equiv.mapTo h φ) f

theorem mapHom_hom (φ : X ⟶ Y) {a b : RoundBicat X n} (p : Arrow a b) :
    mapHom φ p.hom = (p.mapTo φ).hom :=
  rfl

theorem Hom.Mem.mapTo (φ : X ⟶ Y) {a b : RoundBicat X n} {f : a ⟶ b}
    {x : PastingDiagram X} (hx : f.Mem x) : (mapHom φ f).Mem (x.mapTo φ) := by
  obtain ⟨p, rfl⟩ := Arrow.hom_surjective f
  exact (Arrow.mem_hom _ _).2 (((Arrow.mem_hom p x).1 hx).mapTo φ)

theorem mapHom_id (φ : X ⟶ Y) (a : RoundBicat X n) : mapHom φ (𝟙 a) = 𝟙 (mapObj φ a) :=
  (Arrow.hom_eq_hom_iff _ _).2 (equiv_unit_mapTo _ φ)

theorem mapHom_comp (φ : X ⟶ Y) {a b c : RoundBicat X n} (f : a ⟶ b) (g : b ⟶ c) :
    mapHom φ (f ≫ g) = mapHom φ f ≫ mapHom φ g := by
  obtain ⟨p, rfl⟩ := Arrow.hom_surjective f
  obtain ⟨q, rfl⟩ := Arrow.hom_surjective g
  rw [Arrow.hom_comp_hom, mapHom_hom, mapHom_hom, mapHom_hom, Arrow.hom_comp_hom,
    Arrow.hom_eq_hom_iff]
  exact paste_mapTo _ _ _ (p.hasBdry.pastable q.hasBdry (.refl _)) φ
    ((p.mapTo φ).hasBdry.pastable (q.mapTo φ).hasBdry (.refl _))

variable {a b c : RoundBicat X n} {f g h : a ⟶ b}

def Cell.mapTo (φ : X ⟶ Y) (t : Cell f g) : Cell (mapHom φ f) (mapHom φ g) where
  diag := t.diag.mapTo φ
  dim_diag := t.dim_diag
  source := (t.source.mapTo φ).of_equiv (PastingDiagram.Equiv.mapTo_boundary (.refl _) φ).symm
  target := (t.target.mapTo φ).of_equiv (PastingDiagram.Equiv.mapTo_boundary (.refl _) φ).symm

def mapHom₂ (φ : X ⟶ Y) (η : f ⟶ g) : mapHom φ f ⟶ mapHom φ g :=
  Quotient.map (sa := Cell.setoid f g) (sb := Cell.setoid _ _) (Cell.mapTo φ)
    (fun _ _ h => Equivalent.map φ h) η

theorem mapHom₂_homMk (φ : X ⟶ Y) (t : Cell f g) : mapHom₂ φ (homMk t) = homMk (t.mapTo φ) :=
  rfl

theorem mapHom₂_id (φ : X ⟶ Y) (f : a ⟶ b) : mapHom₂ φ (𝟙 f) = 𝟙 (mapHom φ f) := by
  rw [id_eq_homMk, mapHom₂_homMk, ← homMk_unit_of_mem (f.mem_rep.mapTo φ)]
  exact homMk_congr (equiv_unit_mapTo _ φ)

@[reassoc]
theorem mapHom₂_comp (φ : X ⟶ Y) (η : f ⟶ g) (θ : g ⟶ h) :
    mapHom₂ φ (η ≫ θ) = mapHom₂ φ η ≫ mapHom₂ φ θ := by
  obtain ⟨t, rfl⟩ := homMk_surjective η
  obtain ⟨s, rfl⟩ := homMk_surjective θ
  rw [homMk_comp_homMk, mapHom₂_homMk, mapHom₂_homMk, mapHom₂_homMk, homMk_comp_homMk]
  exact homMk_congr (paste_mapTo _ _ _ (t.pastable s) φ ((t.mapTo φ).pastable (s.mapTo φ)))

theorem mapHom₂_eqToHom (φ : X ⟶ Y) {f g : a ⟶ b} (p : f = g) :
    mapHom₂ φ (eqToHom p) = eqToHom (congrArg (mapHom φ) p) := by
  subst p
  exact mapHom₂_id φ f

theorem mapHom₂_whiskerLeft (φ : X ⟶ Y) (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    mapHom₂ φ (f ◁ η) = eqToHom (mapHom_comp φ f g) ≫ mapHom φ f ◁ mapHom₂ φ η ≫
      eqToHom (mapHom_comp φ f h).symm := by
  obtain ⟨t, rfl⟩ := homMk_surjective η
  rw [whiskerLeft_homMk_of_mem f.mem_rep t, mapHom₂_homMk, mapHom₂_homMk,
    whiskerLeft_homMk_of_mem (f.mem_rep.mapTo φ) (t.mapTo φ)]
  have hp := f.mem_rep.pastable_left t.dim_diag t.source
  have hk : n + 1 < (f.rep.diag.paste t.diag.toPastingDiagram n hp).dim := by
    rw [dim_paste, t.dim_diag]; omega
  exact homMk_eq_eqToHom_comp_homMk_comp_eqToHom (mapHom_comp φ f g) (mapHom_comp φ f h) _ _
    (equivalent_of_equiv ((equiv_rounding_mapTo _ hk φ).trans (PastingDiagram.Equiv.rounding
      (paste_mapTo _ _ _ hp φ ((f.mem_rep.mapTo φ).pastable_left (t.mapTo φ).dim_diag
        (t.mapTo φ).source)) hk)))

theorem mapHom₂_whiskerRight (φ : X ⟶ Y) {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    mapHom₂ φ (η ▷ h) = eqToHom (mapHom_comp φ f h) ≫ mapHom₂ φ η ▷ mapHom φ h ≫
      eqToHom (mapHom_comp φ g h).symm := by
  obtain ⟨t, rfl⟩ := homMk_surjective η
  rw [homMk_whiskerRight_of_mem h.mem_rep t, mapHom₂_homMk, mapHom₂_homMk,
    homMk_whiskerRight_of_mem (h.mem_rep.mapTo φ) (t.mapTo φ)]
  have hp := h.mem_rep.pastable_right t.dim_diag t.target
  have hk : n + 1 < (t.diag.paste h.rep.diag.toPastingDiagram n hp).dim := by
    rw [dim_paste, t.dim_diag]; omega
  exact homMk_eq_eqToHom_comp_homMk_comp_eqToHom (mapHom_comp φ f h) (mapHom_comp φ g h) _ _
    (equivalent_of_equiv ((equiv_rounding_mapTo _ hk φ).trans (PastingDiagram.Equiv.rounding
      (paste_mapTo _ _ _ hp φ ((h.mem_rep.mapTo φ).pastable_right (t.mapTo φ).dim_diag
        (t.mapTo φ).target)) hk)))

theorem unitorSpec_fam_mapTo (φ : X ⟶ Y) (α : Bool) {f : a ⟶ b} {x : PastingDiagram X}
    (hx : f.Mem x) :
    ((unitorSpec α a b).fam x).mapTo φ =
      (unitorSpec α (mapObj φ a) (mapObj φ b)).fam (x.mapTo φ) := by
  rw [CylSpec.fam_def, CylSpec.fam_def, cylDiagram_congr _ (unitorSpec_K α hx),
    cylDiagram_congr _ (unitorSpec_K α (hx.mapTo φ))]
  exact congrArg (PastingDiagram.mk _) (Category.assoc _ _ _)

theorem equiv_unitorSpec_fam_mapTo (φ : X ⟶ Y) (α : Bool) (f : a ⟶ b) :
    (((unitorSpec α a b).fam f.rep.diag.toPastingDiagram).mapTo φ).Equiv
      ((unitorSpec α (mapObj φ a) (mapObj φ b)).fam (mapHom φ f).rep.diag.toPastingDiagram) := by
  have hm := (mapHom φ f).mem_rep
  have hs : ((mapHom φ f).rep.diag.boundary n α).Equiv
      (unitorSpec α (mapObj φ a) (mapObj φ b)).z := by
    cases α
    · exact hm.hasBdry.side
    · exact hm.hasBdry.other
  have hfit : (unitorSpec α (mapObj φ a) (mapObj φ b)).Fits
      (mapHom φ f).rep.diag.toPastingDiagram :=
    ⟨hm.isRound, by rw [hm.dim_eq]; exact n.lt_succ_self, hs⟩
  have e := (CylSpec.fam_equiv hfit (hm.equiv (f.mem_rep.mapTo φ))).symm
  rw [unitorSpec_fam_mapTo φ α f.mem_rep]
  exact e

theorem mapHom₂_leftUnitor_inv (φ : X ⟶ Y) (f : a ⟶ b) :
    mapHom₂ φ (λ_ f).inv = (λ_ (mapHom φ f)).inv ≫
      eqToHom (by rw [mapHom_comp, mapHom_id]) := by
  have h₁ : (λ_ f).inv = homMk (Cell.leftUnitor f) := rfl
  have h₂ : (λ_ (mapHom φ f)).inv = homMk (Cell.leftUnitor (mapHom φ f)) := rfl
  rw [h₁, h₂, mapHom₂_homMk]
  refine (homMk_eq_eqToHom_comp_homMk_comp_eqToHom rfl
    (by rw [mapHom_comp, mapHom_id]) _ (Cell.leftUnitor (mapHom φ f))
    (equivalent_of_equiv (equiv_unitorSpec_fam_mapTo φ false f))).trans ?_
  rw [eqToHom_refl, Category.id_comp]

theorem mapHom₂_leftUnitor (φ : X ⟶ Y) (f : a ⟶ b) :
    mapHom₂ φ (λ_ f).hom = eqToHom (by rw [mapHom_comp, mapHom_id]) ≫ (λ_ (mapHom φ f)).hom := by
  have h : mapHom₂ φ (λ_ f).hom ≫ mapHom₂ φ (λ_ f).inv = 𝟙 _ := by
    rw [← mapHom₂_comp, Iso.hom_inv_id, mapHom₂_id]
  rw [mapHom₂_leftUnitor_inv] at h
  simpa using congrArg (· ≫ eqToHom (by rw [mapHom_comp, mapHom_id]) ≫ (λ_ (mapHom φ f)).hom) h

theorem mapHom₂_rightUnitor (φ : X ⟶ Y) (f : a ⟶ b) :
    mapHom₂ φ (ρ_ f).hom = eqToHom (by rw [mapHom_comp, mapHom_id]) ≫ (ρ_ (mapHom φ f)).hom := by
  have h₁ : (ρ_ f).hom = homMk (Cell.rightUnitor f) := rfl
  have h₂ : (ρ_ (mapHom φ f)).hom = homMk (Cell.rightUnitor (mapHom φ f)) := rfl
  rw [h₁, h₂, mapHom₂_homMk]
  refine (homMk_eq_eqToHom_comp_homMk_comp_eqToHom (by rw [mapHom_comp, mapHom_id]) rfl
    _ (Cell.rightUnitor (mapHom φ f))
    (equivalent_of_equiv (equiv_unitorSpec_fam_mapTo φ true f))).trans ?_
  rw [eqToHom_refl, Category.comp_id]

theorem mapHom₂_associator (φ : X ⟶ Y) {d : RoundBicat X n} (f : a ⟶ b) (g : b ⟶ c)
    (h : c ⟶ d) :
    mapHom₂ φ (α_ f g h).hom = eqToHom (by simp only [mapHom_comp]) ≫
      (α_ (mapHom φ f) (mapHom φ g) (mapHom φ h)).hom ≫ eqToHom (by simp only [mapHom_comp]) := by
  rw [associator_hom, associator_hom, mapHom₂_eqToHom, eqToHom_trans, eqToHom_trans]

noncomputable def map (φ : X ⟶ Y) : StrictPseudofunctor (RoundBicat X n) (RoundBicat Y n) :=
  StrictPseudofunctor.mk'
    { obj := mapObj φ
      map := mapHom φ
      map₂ := mapHom₂ φ
      map₂_id := mapHom₂_id φ
      map₂_comp := mapHom₂_comp φ
      map_id := mapHom_id φ
      map_comp := mapHom_comp φ
      map₂_whisker_left := mapHom₂_whiskerLeft φ
      map₂_whisker_right := mapHom₂_whiskerRight φ
      map₂_left_unitor := mapHom₂_leftUnitor φ
      map₂_right_unitor := mapHom₂_rightUnitor φ
      map₂_associator := mapHom₂_associator φ }

theorem map_map₂_homMk (φ : X ⟶ Y) (t : Cell f g) :
    (map φ).map₂ (homMk t) = homMk (t.mapTo φ) :=
  rfl

theorem map_id_obj (a : RoundBicat X n) : (map (𝟙 X)).obj a = a :=
  ext_diag (PastingDiagram.mapTo_id _)

theorem map_comp_obj (φ : X ⟶ Y) (ψ : Y ⟶ Z) (a : RoundBicat X n) :
    (map (φ ≫ ψ)).obj a = (map ψ).obj ((map φ).obj a) :=
  ext_diag (mapTo_comp _ φ ψ)

theorem map_id_map (f : a ⟶ b) : (map (𝟙 X)).map f ≍ f := by
  obtain ⟨p, rfl⟩ := Arrow.hom_surjective f
  refine Arrow.hom_heq (map_id_obj a) (map_id_obj b) (p.mapTo (𝟙 X)) p ?_
  change (p.diag.toPastingDiagram.mapTo (𝟙 X)).Equiv _
  rw [p.diag.toPastingDiagram.mapTo_id]

theorem map_comp_map (φ : X ⟶ Y) (ψ : Y ⟶ Z) (f : a ⟶ b) :
    (map (φ ≫ ψ)).map f ≍ (map ψ).map ((map φ).map f) := by
  obtain ⟨p, rfl⟩ := Arrow.hom_surjective f
  refine Arrow.hom_heq (map_comp_obj φ ψ a) (map_comp_obj φ ψ b) (p.mapTo (φ ≫ ψ))
    ((p.mapTo φ).mapTo ψ) ?_
  change (p.diag.toPastingDiagram.mapTo (φ ≫ ψ)).Equiv _
  rw [mapTo_comp]
  exact .refl _

theorem map_id : map (n := n) (𝟙 X) = StrictPseudofunctor.id (RoundBicat X n) :=
  StrictPseudofunctor.ext_of_heq map_id_obj map_id_map fun {a b f g} η => by
    obtain ⟨t, rfl⟩ := homMk_surjective η
    refine homMk_heq (map_id_obj a) (map_id_obj b) (map_id_map f) (map_id_map g)
      (t.mapTo (𝟙 X)) t (equivalent_of_equiv ?_)
    change (t.diag.toPastingDiagram.mapTo (𝟙 X)).Equiv _
    rw [t.diag.toPastingDiagram.mapTo_id]

theorem map_comp (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    map (n := n) (φ ≫ ψ) = (map φ).comp (map ψ) :=
  StrictPseudofunctor.ext_of_heq (map_comp_obj φ ψ) (map_comp_map φ ψ) fun {a b f g} η => by
    obtain ⟨t, rfl⟩ := homMk_surjective η
    refine homMk_heq (map_comp_obj φ ψ a) (map_comp_obj φ ψ b) (map_comp_map φ ψ f)
      (map_comp_map φ ψ g) (t.mapTo (φ ≫ ψ)) ((t.mapTo φ).mapTo ψ) (equivalent_of_equiv ?_)
    change (t.diag.toPastingDiagram.mapTo (φ ≫ ψ)).Equiv _
    rw [mapTo_comp]
    exact .refl _

theorem exists_equivalence_map (φ : X ⟶ Y) (e : Bicategory.Equivalence a b) :
    ∃ e' : Bicategory.Equivalence ((map φ).obj a) ((map φ).obj b),
      e'.hom = (map (n := n) φ).map e.hom :=
  ⟨(map φ).mapEquivalence e, rfl⟩

def Cell.mapToOf (φ : X ⟶ Y) {f g : a ⟶ b} {f' g' : mapObj φ a ⟶ mapObj φ b}
    (hf : mapHom φ f = f') (hg : mapHom φ g = g') (t : Cell f g) : Cell f' g' where
  diag := t.diag.mapTo φ
  dim_diag := t.dim_diag
  source := hf ▸ (t.mapTo φ).source
  target := hg ▸ (t.mapTo φ).target

theorem homMk_mapToOf (φ : X ⟶ Y) {f g : a ⟶ b} {f' g' : mapObj φ a ⟶ mapObj φ b}
    (hf : mapHom φ f = f') (hg : mapHom φ g = g') (t : Cell f g) :
    homMk (t.mapToOf φ hf hg) = eqToHom hf.symm ≫ (map φ).map₂ (homMk t) ≫ eqToHom hg := by
  exact homMk_eq_eqToHom_comp_homMk_comp_eqToHom hf.symm hg.symm _ (t.mapTo φ) (equivalent_refl _)

theorem exists_adjoint_invertors_mapTo (φ : X ⟶ Y) (p : Arrow a b) (q : Arrow b a)
    (z : Cell (p.hom ≫ q.hom) (𝟙 a)) (h : Cell (𝟙 b) (q.hom ≫ p.hom))
    (t₁ : (ρ_ p.hom).inv ≫ p.hom ◁ homMk h ≫ (α_ p.hom q.hom p.hom).inv ≫ homMk z ▷ p.hom ≫
      (λ_ p.hom).hom = 𝟙 p.hom)
    (t₂ : (λ_ q.hom).inv ≫ homMk h ▷ q.hom ≫ (α_ q.hom p.hom q.hom).hom ≫ q.hom ◁ homMk z ≫
      (ρ_ q.hom).hom = 𝟙 q.hom) :
    ∃ (z' : Cell ((p.mapTo φ).hom ≫ (q.mapTo φ).hom) (𝟙 (mapObj φ a)))
      (h' : Cell (𝟙 (mapObj φ b)) ((q.mapTo φ).hom ≫ (p.mapTo φ).hom)),
      z'.diag = z.diag.mapTo φ ∧ h'.diag = h.diag.mapTo φ ∧
      (ρ_ (p.mapTo φ).hom).inv ≫ (p.mapTo φ).hom ◁ homMk h' ≫
          (α_ (p.mapTo φ).hom (q.mapTo φ).hom (p.mapTo φ).hom).inv ≫
          homMk z' ▷ (p.mapTo φ).hom ≫ (λ_ (p.mapTo φ).hom).hom = 𝟙 (p.mapTo φ).hom ∧
      (λ_ (q.mapTo φ).hom).inv ≫ homMk h' ▷ (q.mapTo φ).hom ≫
          (α_ (q.mapTo φ).hom (p.mapTo φ).hom (q.mapTo φ).hom).hom ≫
          (q.mapTo φ).hom ◁ homMk z' ≫ (ρ_ (q.mapTo φ).hom).hom = 𝟙 (q.mapTo φ).hom := by
  obtain ⟨adj, hu, hc⟩ : ∃ adj : q.hom ⊣ p.hom, adj.unit = homMk h ∧ adj.counit = homMk z :=
    ⟨.ofUnitorTriangles (homMk h) (homMk z) t₂ t₁, rfl, rfl⟩
  have hz : homMk (z.mapToOf φ (mapHom_comp φ p.hom q.hom) (mapHom_id φ a)) =
      ((map φ).mapAdjunction adj).counit := by
    rw [homMk_mapToOf, StrictPseudofunctor.mapAdjunction_counit', hc]
    rfl
  have hh : homMk (h.mapToOf φ (mapHom_id φ b) (mapHom_comp φ q.hom p.hom)) =
      ((map φ).mapAdjunction adj).unit := by
    rw [homMk_mapToOf, StrictPseudofunctor.mapAdjunction_unit', hu]
    rfl
  refine ⟨z.mapToOf φ (mapHom_comp φ p.hom q.hom) (mapHom_id φ a),
    h.mapToOf φ (mapHom_id φ b) (mapHom_comp φ q.hom p.hom), rfl, rfl, ?_, ?_⟩
  · have := Adjunction.rightZigzag_eq_iff.1 ((map φ).mapAdjunction adj).right_triangle
    rwa [← hz, ← hh] at this
  · have := Adjunction.leftZigzag_eq_iff.1 ((map φ).mapAdjunction adj).left_triangle
    rwa [← hz, ← hh] at this

end RoundBicat

end Atoms.Diagrammatic

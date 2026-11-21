import Atoms.ForMathlib.CategoryTheory.Bicategory.Coherence
import Atoms.ForMathlib.CategoryTheory.EqToHom

namespace CategoryTheory.FreeBicategory

universe w v u v₂ u₂

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

section Structural

variable {W : Type u₂} [Quiver.{v₂} W] (F : Prefunctor W B) {a b : FreeBicategory W}

def IsStructural (X Y : a ⟶ b) {U U' : (lift F).obj a ⟶ (lift F).obj b} (φ : U ⟶ U') : Prop :=
  ∃ (θ : X ⟶ Y) (hU : U = (lift F).map X) (hU' : (lift F).map Y = U'),
    φ = eqToHom hU ≫ (lift F).map₂ θ ≫ eqToHom hU'

def IsSandwich (X Y : a ⟶ b) {X' Y' : a ⟶ b} (C : (lift F).map X' ⟶ (lift F).map Y')
    {U U' : (lift F).obj a ⟶ (lift F).obj b} (φ : U ⟶ U') : Prop :=
  ∃ (θ₁ : X ⟶ X') (θ₂ : Y' ⟶ Y) (hU : U = (lift F).map X) (hU' : (lift F).map Y = U'),
    φ = eqToHom hU ≫ (lift F).map₂ θ₁ ≫ C ≫ (lift F).map₂ θ₂ ≫ eqToHom hU'

variable {F} {X Y Z X' Y' : a ⟶ b} {C : (lift F).map X' ⟶ (lift F).map Y'}
  {U U' U'' : (lift F).obj a ⟶ (lift F).obj b}

theorem IsStructural.heq_id {φ : U ⟶ U'} (hφ : IsStructural F X X φ) : φ ≍ 𝟙 U := by
  obtain ⟨θ, hU, hU', rfl⟩ := hφ
  obtain rfl : θ = 𝟙 X := Subsingleton.elim _ _
  subst hU hU'
  simp only [PrelaxFunctor.map₂_id, eqToHom_refl, Category.comp_id]
  rfl

theorem IsStructural.eq {φ ψ : U ⟶ U'} (hφ : IsStructural F X Y φ)
    (hψ : IsStructural F X Y ψ) : φ = ψ := by
  obtain ⟨θ, hU, hU', rfl⟩ := hφ
  obtain ⟨θ', -, -, rfl⟩ := hψ
  rw [Subsingleton.elim θ θ']

theorem IsStructural.heq {V V' : (lift F).obj a ⟶ (lift F).obj b} {φ : U ⟶ U'} {ψ : V ⟶ V'}
    (hφ : IsStructural F X Y φ) (hψ : IsStructural F X Y ψ) : φ ≍ ψ := by
  obtain ⟨θ, hU, hU', rfl⟩ := hφ
  obtain ⟨θ', hV, hV', rfl⟩ := hψ
  rw [Subsingleton.elim θ θ']
  exact ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).trans
    ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm

theorem IsStructural.heq_of_eq {G : Prefunctor W B} (hG : F = G)
    {V V' : (lift G).obj a ⟶ (lift G).obj b} {φ : U ⟶ U'} {ψ : V ⟶ V'}
    (hφ : IsStructural F X Y φ) (hψ : IsStructural G X Y ψ) : φ ≍ ψ := by
  subst hG
  exact hφ.heq hψ

theorem IsSandwich.eq {φ ψ : U ⟶ U'} (hφ : IsSandwich F X Y C φ) (hψ : IsSandwich F X Y C ψ) :
    φ = ψ := by
  obtain ⟨θ₁, θ₂, hU, hU', rfl⟩ := hφ
  obtain ⟨θ₁', θ₂', -, -, rfl⟩ := hψ
  rw [Subsingleton.elim θ₁ θ₁', Subsingleton.elim θ₂ θ₂']

theorem isStructural_map₂ (θ : X ⟶ Y) : IsStructural F X Y ((lift F).map₂ θ) :=
  ⟨θ, rfl, rfl, by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]⟩

theorem isStructural_id (hU : U = (lift F).map X) : IsStructural F X X (𝟙 U) :=
  ⟨𝟙 X, hU, hU.symm, by
    subst hU
    simp only [eqToHom_refl, PrelaxFunctor.map₂_id, Category.comp_id]⟩

theorem isStructural_eqToHom {W : Type*} [Quiver W] {G : Prefunctor W B}
    {a b : FreeBicategory W} {X : a ⟶ b} {U U' : (lift G).obj a ⟶ (lift G).obj b}
    (hU : U = (lift G).map X) (h : U = U') : IsStructural G X X (eqToHom h) :=
  ⟨𝟙 X, hU, hU.symm.trans h, by
    subst h hU
    simp only [eqToHom_refl, PrelaxFunctor.map₂_id, Category.comp_id]⟩

theorem nf_eq_of_isStructural {W : Type*} [Quiver W] {G : Prefunctor W B}
    {a b : FreeBicategory W} {X Y : a ⟶ b} {U U' : (lift G).obj a ⟶ (lift G).obj b} {φ : U ⟶ U'}
    (h : IsStructural G X Y φ) : normalizeAux .nil X = normalizeAux .nil Y :=
  h.elim fun θ _ => normalizeAux_congr _ θ

theorem IsStructural.comp {φ : U ⟶ U'} {ψ : U' ⟶ U''} (hφ : IsStructural F X Y φ)
    (hψ : IsStructural F Y Z ψ) : IsStructural F X Z (φ ≫ ψ) := by
  obtain ⟨θ, hU, hU', rfl⟩ := hφ
  obtain ⟨θ', hV, hV', rfl⟩ := hψ
  refine ⟨θ ≫ θ', hU, hV', ?_⟩
  subst hU'
  simp only [Category.assoc, eqToHom_refl, Category.id_comp, PrelaxFunctor.map₂_comp]

theorem IsStructural.comp_isSandwich {φ : U ⟶ U'} {ψ : U' ⟶ U''} (hφ : IsStructural F X Y φ)
    (hψ : IsSandwich F Y Z C ψ) : IsSandwich F X Z C (φ ≫ ψ) := by
  obtain ⟨θ, hU, hU', rfl⟩ := hφ
  obtain ⟨θ₁, θ₂, hV, hV', rfl⟩ := hψ
  refine ⟨θ ≫ θ₁, θ₂, hU, hV', ?_⟩
  subst hU'
  simp only [Category.assoc, eqToHom_refl, Category.id_comp, PrelaxFunctor.map₂_comp]

theorem IsSandwich.comp_isStructural {φ : U ⟶ U'} {ψ : U' ⟶ U''} (hφ : IsSandwich F X Y C φ)
    (hψ : IsStructural F Y Z ψ) : IsSandwich F X Z C (φ ≫ ψ) := by
  obtain ⟨θ₁, θ₂, hU, hU', rfl⟩ := hφ
  obtain ⟨θ, hV, hV', rfl⟩ := hψ
  refine ⟨θ₁, θ₂ ≫ θ, hU, hV', ?_⟩
  subst hU'
  simp only [Category.assoc, eqToHom_refl, Category.id_comp, PrelaxFunctor.map₂_comp]

theorem IsStructural.eqToHom_comp {U₀ : (lift F).obj a ⟶ (lift F).obj b} {φ : U ⟶ U'}
    (h : U₀ = U) (hφ : IsStructural F X Y φ) : IsStructural F X Y (eqToHom h ≫ φ) := by
  obtain ⟨θ, hU, hU', rfl⟩ := hφ
  exact ⟨θ, h.trans hU, hU', eqToHom_trans_assoc _ _ _⟩

theorem IsStructural.comp_eqToHom {φ : U ⟶ U'} (hφ : IsStructural F X Y φ) (h : U' = U'') :
    IsStructural F X Y (φ ≫ eqToHom h) := by
  obtain ⟨θ, hU, hU', rfl⟩ := hφ
  exact ⟨θ, hU, hU'.trans h, by simp only [Category.assoc, eqToHom_trans]⟩

theorem IsSandwich.eqToHom_comp {U₀ : (lift F).obj a ⟶ (lift F).obj b} {φ : U ⟶ U'}
    (h : U₀ = U) (hφ : IsSandwich F X Y C φ) : IsSandwich F X Y C (eqToHom h ≫ φ) := by
  obtain ⟨θ₁, θ₂, hU, hU', rfl⟩ := hφ
  exact ⟨θ₁, θ₂, h.trans hU, hU', eqToHom_trans_assoc _ _ _⟩

theorem IsSandwich.comp_eqToHom {φ : U ⟶ U'} (hφ : IsSandwich F X Y C φ) (h : U' = U'') :
    IsSandwich F X Y C (φ ≫ eqToHom h) := by
  obtain ⟨θ₁, θ₂, hU, hU', rfl⟩ := hφ
  exact ⟨θ₁, θ₂, hU, hU'.trans h, by simp only [Category.assoc, eqToHom_trans]⟩

theorem isSandwich_comp_comp {X₀ Y₀ : a ⟶ b} {D : (lift F).map X₀ ⟶ (lift F).map Y₀}
    {U₀ U₁ U₂ U₃ U₄ U₅ : (lift F).obj a ⟶ (lift F).obj b} {A : U₁ ⟶ U₂} {C' : U₂ ⟶ U₃}
    {B' : U₃ ⟶ U₄} (h : U₀ = U₁) (hA : IsStructural F X X' A) (hC : IsSandwich F X' Y' D C')
    (hB : IsStructural F Y' Y B') (h' : U₄ = U₅) :
    IsSandwich F X Y D (eqToHom h ≫ A ≫ C' ≫ B' ≫ eqToHom h') := by
  obtain ⟨θ, hU, hU', rfl⟩ := hA
  obtain ⟨θ₁, θ₂, hV, hV', rfl⟩ := hC
  obtain ⟨ζ, hW, hW', rfl⟩ := hB
  refine ⟨θ ≫ θ₁, θ₂ ≫ ζ, h.trans hU, hW'.trans h', ?_⟩
  subst hU' hV' hW'
  simp only [Category.assoc, eqToHom_refl, Category.id_comp, PrelaxFunctor.map₂_comp,
    eqToHom_trans_assoc]

theorem isStructural_comp_comp {U₀ U₁ U₂ U₃ U₄ U₅ : (lift F).obj a ⟶ (lift F).obj b}
    {A : U₁ ⟶ U₂} {C' : U₂ ⟶ U₃} {B' : U₃ ⟶ U₄} (h : U₀ = U₁) (hA : IsStructural F X X' A)
    (hC : IsStructural F X' Y' C') (hB : IsStructural F Y' Y B') (h' : U₄ = U₅) :
    IsStructural F X Y (eqToHom h ≫ A ≫ C' ≫ B' ≫ eqToHom h') := by
  obtain ⟨θ, hU, hU', rfl⟩ := hA
  obtain ⟨θ₁, hV, hV', rfl⟩ := hC
  obtain ⟨ζ, hW, hW', rfl⟩ := hB
  refine ⟨θ ≫ θ₁ ≫ ζ, h.trans hU, hW'.trans h', ?_⟩
  subst hU' hV' hW'
  simp only [Category.assoc, eqToHom_refl, Category.id_comp, PrelaxFunctor.map₂_comp,
    eqToHom_trans_assoc]

theorem isSandwich_of_eq (θ₁ : X ⟶ X') (θ₂ : Y' ⟶ Y) {φ : (lift F).map X ⟶ (lift F).map Y}
    (h : φ = (lift F).map₂ θ₁ ≫ C ≫ (lift F).map₂ θ₂) : IsSandwich F X Y C φ :=
  ⟨θ₁, θ₂, rfl, rfl, by simp only [h, eqToHom_refl, Category.id_comp, Category.comp_id]⟩

theorem IsSandwich.trans {X₀ Y₀ : a ⟶ b} {D : (lift F).map X₀ ⟶ (lift F).map Y₀}
    {φ : U ⟶ U'} (hφ : IsSandwich F X Y C φ) (hC : IsSandwich F X' Y' D C) :
    IsSandwich F X Y D φ := by
  obtain ⟨θ₁, θ₂, hU, hU', rfl⟩ := hφ
  obtain ⟨ζ₁, ζ₂, hV, hV', hCe⟩ := hC
  refine ⟨θ₁ ≫ ζ₁, ζ₂ ≫ θ₂, hU, hU', ?_⟩
  rw [hCe]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc,
    PrelaxFunctor.map₂_comp]

theorem IsStructural.congr {X₂ Y₂ : a ⟶ b} {φ : U ⟶ U'} (hφ : IsStructural F X Y φ)
    (hX : X = X₂) (hY : Y = Y₂) : IsStructural F X₂ Y₂ φ := by
  subst hX hY
  exact hφ

theorem IsSandwich.congr {X₂ Y₂ : a ⟶ b} {φ : U ⟶ U'} (hφ : IsSandwich F X Y C φ) (hX : X = X₂)
    (hY : Y = Y₂) : IsSandwich F X₂ Y₂ C φ := by
  subst hX hY
  exact hφ

theorem isSandwich_self (hX : X = X') (hY : Y' = Y) : IsSandwich F X Y C C :=
  ⟨eqToHom hX, eqToHom hY, congrArg _ hX.symm, congrArg _ hY.symm, by
    subst hX hY
    simp only [eqToHom_refl, PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id]⟩

theorem isSandwich_conj {W : Type*} [Quiver W] {G : Prefunctor W B}
    {a b : FreeBicategory W} {X Y : a ⟶ b} {U U' : (lift G).obj a ⟶ (lift G).obj b}
    (hU : U = (lift G).map X) (C : (lift G).map X ⟶ (lift G).map Y) (hU' : (lift G).map Y = U') :
    IsSandwich G X Y C (eqToHom hU ≫ C ≫ eqToHom hU') :=
  ⟨𝟙 _, 𝟙 _, hU, hU', by simp only [PrelaxFunctor.map₂_id, Category.id_comp]⟩

theorem IsSandwich.congr_whisker {c d : FreeBicategory W} {Xp Xp' : a ⟶ c} {Xr Xr' : d ⟶ b}
    {Y₀ Y₀' : c ⟶ d} {D : (lift F).map Y₀ ⟶ (lift F).map Y₀'} {φ : U ⟶ U'}
    (hφ : IsSandwich F X Y (X' := Xp ≫ Y₀ ≫ Xr) (Y' := Xp ≫ Y₀' ≫ Xr)
      ((lift F).map Xp ◁ (D ▷ (lift F).map Xr)) φ) (hp : Xp = Xp') (hr : Xr = Xr') :
    IsSandwich F X Y (X' := Xp' ≫ Y₀ ≫ Xr') (Y' := Xp' ≫ Y₀' ≫ Xr')
      ((lift F).map Xp' ◁ (D ▷ (lift F).map Xr')) φ := by
  subst hp hr
  exact hφ

variable (F) in
theorem isStructural_leftUnitor_inv (X : a ⟶ b) {U : (lift F).obj a ⟶ (lift F).obj b}
    (hU : U = (lift F).map X) :
    IsStructural F X (𝟙 a ≫ X) (λ_ U).inv := by
  subst hU
  exact ⟨(λ_ X).inv, rfl, rfl, ((Category.id_comp _).trans (Category.comp_id _)).symm⟩

variable (F) in
theorem isStructural_leftUnitor_hom (X : a ⟶ b) {U : (lift F).obj a ⟶ (lift F).obj b}
    (hU : U = (lift F).map X) :
    IsStructural F (𝟙 a ≫ X) X (λ_ U).hom := by
  subst hU
  exact ⟨(λ_ X).hom, rfl, rfl, ((Category.id_comp _).trans (Category.comp_id _)).symm⟩

variable (F) in
theorem isStructural_rightUnitor_hom (X : a ⟶ b) {U : (lift F).obj a ⟶ (lift F).obj b}
    (hU : U = (lift F).map X) :
    IsStructural F (X ≫ 𝟙 b) X (ρ_ U).hom := by
  subst hU
  exact ⟨(ρ_ X).hom, rfl, rfl, ((Category.id_comp _).trans (Category.comp_id _)).symm⟩

theorem IsStructural.whiskerRight_of_eq {c : FreeBicategory W} {X Y : a ⟶ b}
    {U U' : (lift F).obj a ⟶ (lift F).obj b} {φ : U ⟶ U'} (hφ : IsStructural F X Y φ)
    (Z : b ⟶ c) {V : (lift F).obj b ⟶ (lift F).obj c} (hV : V = (lift F).map Z) :
    IsStructural F (X ≫ Z) (Y ≫ Z) (φ ▷ V) := by
  obtain ⟨θ, hU, hU', rfl⟩ := hφ
  subst hU hU' hV
  refine ⟨θ ▷ Z, rfl, rfl, ?_⟩
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, lift_map₂_whiskerRight]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

theorem IsStructural.whiskerLeft_of_eq {c : FreeBicategory W} {X Y : b ⟶ c}
    {U U' : (lift F).obj b ⟶ (lift F).obj c} {φ : U ⟶ U'} (hφ : IsStructural F X Y φ)
    (Z : a ⟶ b) {V : (lift F).obj a ⟶ (lift F).obj b} (hV : V = (lift F).map Z) :
    IsStructural F (Z ≫ X) (Z ≫ Y) (V ◁ φ) := by
  obtain ⟨θ, hU, hU', rfl⟩ := hφ
  subst hU hU' hV
  refine ⟨Z ◁ θ, rfl, rfl, ?_⟩
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, lift_map₂_whiskerLeft]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

theorem IsStructural.of_heq {V V' : (lift F).obj a ⟶ (lift F).obj b} {φ : U ⟶ U'}
    (hφ : IsStructural F X Y φ) {ψ : V ⟶ V'} (hV : V = U) (hV' : V' = U') (h : ψ ≍ φ) :
    IsStructural F X Y ψ := by
  subst hV hV'
  rwa [eq_of_heq h]

end Structural

section Lift

variable {V : Type*} [Quiver V] {W : Type u₂} [Quiver.{v₂} W]
  {G : Prefunctor V (FreeBicategory W)} {F : Prefunctor W B} {a b : FreeBicategory V}

theorem IsStructural.of_comp_lift {X Y : a ⟶ b}
    {U U' : (lift (G ⋙q (lift F).toPrefunctor)).obj a ⟶ (lift (G ⋙q (lift F).toPrefunctor)).obj b}
    {φ : U ⟶ U'} (h : IsStructural (G ⋙q (lift F).toPrefunctor) X Y φ) :
    IsStructural F ((lift G).map X) ((lift G).map Y) φ := by
  obtain ⟨θ, hU, hU', rfl⟩ := h
  exact ⟨(lift G).map₂ θ, hU.trans (lift_map_lift G F X), (lift_map_lift G F Y).symm.trans hU',
    (congrArg (fun z => eqToHom hU ≫ z ≫ eqToHom hU') (lift_map₂_lift G F θ)).trans
      (eqToHom_comp_comp_eqToHom_eq _ _ _ _ _ _ _)⟩

theorem IsStructural.comp_lift {X Y : a ⟶ b}
    {U U' : (lift (G ⋙q (lift F).toPrefunctor)).obj a ⟶ (lift (G ⋙q (lift F).toPrefunctor)).obj b}
    {φ : U ⟶ U'} (h : IsStructural F ((lift G).map X) ((lift G).map Y) φ) (θ : X ⟶ Y) :
    IsStructural (G ⋙q (lift F).toPrefunctor) X Y φ := by
  obtain ⟨θ', hU, hU', rfl⟩ := h
  refine ⟨θ, hU.trans (lift_map_lift G F X).symm, (lift_map_lift G F Y).trans hU', ?_⟩
  rw [lift_map₂_lift, Subsingleton.elim ((lift G).map₂ θ) θ']
  exact (eqToHom_comp_comp_eqToHom_eq _ _ _ _ _ _ _).symm

end Lift

section Whisker

variable {V : Type*} [Quiver V] {W : Type u₂} [Quiver.{v₂} W]
  {G : Prefunctor V (FreeBicategory W)} {F : Prefunctor W B}

private theorem whisker_sandwich {a b c d : B} {A : a ⟶ b} {Q Q₁ Q₂ Q' : b ⟶ c} {R : c ⟶ d}
    {T T' : a ⟶ d} {S S' : b ⟶ d} (Φ : T ⟶ A ≫ S) (Ψ : S ⟶ Q ≫ R) (M₁ : Q ⟶ Q₁) (D : Q₁ ⟶ Q₂)
    (M₂ : Q₂ ⟶ Q') (Ψ' : Q' ≫ R ⟶ S') (Φ' : A ≫ S' ⟶ T') :
    Φ ≫ A ◁ (Ψ ≫ (M₁ ≫ D ≫ M₂) ▷ R ≫ Ψ') ≫ Φ' =
      (Φ ≫ A ◁ Ψ ≫ A ◁ (M₁ ▷ R)) ≫ A ◁ (D ▷ R) ≫ (A ◁ (M₂ ▷ R) ≫ A ◁ Ψ' ≫ Φ') := by
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]

theorem isSandwich_pathWhisker {x y z w : V} (p : Quiver.Path x y) {q q' : Quiver.Path y z}
    (r : Quiver.Path z w) {X' Y' : G.obj y ⟶ G.obj z}
    {D : (lift F).map X' ⟶ (lift F).map Y'}
    {η : pathComp (G ⋙q (lift F).toPrefunctor) q ⟶ pathComp (G ⋙q (lift F).toPrefunctor) q'}
    (hη : IsSandwich F (pathComp G q) (pathComp G q') D η) :
    IsSandwich F (pathComp G (p.comp (q.comp r))) (pathComp G (p.comp (q'.comp r)))
      (X' := pathComp G p ≫ X' ≫ pathComp G r) (Y' := pathComp G p ≫ Y' ≫ pathComp G r)
      ((lift F).map (pathComp G p) ◁ (D ▷ (lift F).map (pathComp G r)))
      (pathWhisker (G ⋙q (lift F).toPrefunctor) p η r) := by
  obtain ⟨θ₁, θ₂, hU, hU', hφ⟩ := hη
  have hφ' : η = eqToHom (pathComp_comp_lift G F q) ≫ ((lift F).map₂ θ₁ ≫ D ≫ (lift F).map₂ θ₂) ≫
      eqToHom (pathComp_comp_lift G F q').symm :=
    hφ.trans (congrArg (eqToHom hU ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg ((lift F).map₂ θ₁ ≫ ·) (Category.assoc _ _ _))).symm)
  rw [hφ']
  have hbr : (lift F).map₂ (pathCompCompIso G p (q.comp r)).hom ≫
      (lift F).map (pathComp G p) ◁ ((lift F).map₂ (pathCompCompIso G q r).hom ≫
        ((lift F).map₂ θ₁ ≫ D ≫ (lift F).map₂ θ₂) ▷ (lift F).map (pathComp G r) ≫
          (lift F).map₂ (pathCompCompIso G q' r).inv) ≫
      (lift F).map₂ (pathCompCompIso G p (q'.comp r)).inv =
      (lift F).map₂ ((pathCompCompIso G p (q.comp r)).hom ≫
        pathComp G p ◁ (pathCompCompIso G q r).hom ≫ pathComp G p ◁ (θ₁ ▷ pathComp G r)) ≫
      ((lift F).map (pathComp G p) ◁ (D ▷ (lift F).map (pathComp G r))) ≫
      (lift F).map₂ (pathComp G p ◁ (θ₂ ▷ pathComp G r) ≫
        pathComp G p ◁ (pathCompCompIso G q' r).inv ≫ (pathCompCompIso G p (q'.comp r)).inv) := by
    refine (whisker_sandwich _ _ _ _ _ _ _).trans ?_
    simp only [PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_whiskerRight,
      Category.assoc]
    exact Category.assoc _ _ _
  exact ⟨_, _, pathComp_comp_lift G F _, (pathComp_comp_lift G F _).symm,
    (pathWhisker_comp_lift G F p _ r).trans ((congrArg (fun z => eqToHom _ ≫ z ≫ eqToHom _)
      hbr).trans (congrArg (eqToHom _ ≫ ·) ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) (Category.assoc _ _ _)))))⟩

theorem isStructural_pathWhisker {x y z w : V} (p : Quiver.Path x y) {q q' : Quiver.Path y z}
    (r : Quiver.Path z w)
    {η : pathComp (G ⋙q (lift F).toPrefunctor) q ⟶ pathComp (G ⋙q (lift F).toPrefunctor) q'}
    (hη : IsStructural F (pathComp G q) (pathComp G q') η) :
    IsStructural F (pathComp G (p.comp (q.comp r))) (pathComp G (p.comp (q'.comp r)))
      (pathWhisker (G ⋙q (lift F).toPrefunctor) p η r) := by
  obtain ⟨θ, hU, hU', rfl⟩ := hη
  refine ⟨pathWhisker G p θ r, pathComp_comp_lift G F _, (pathComp_comp_lift G F _).symm,
    (pathWhisker_comp_lift G F p _ r).trans (congrArg (fun z => eqToHom _ ≫ z ≫ eqToHom _) ?_)⟩
  simp only [pathWhisker, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft,
    lift_map₂_whiskerRight]
  rfl

theorem whiskerLeft_whiskerRight_eq_conj {a b c d : B} {P P' : a ⟶ b} {R R' : c ⟶ d}
    {Y Y' : b ⟶ c} (D : Y ⟶ Y') {σ : P ⟶ P'} {σ' : P' ⟶ P} {τ : R ⟶ R'} {τ' : R' ⟶ R}
    (hσ : σ ≫ σ' = 𝟙 P) (hτ : τ ≫ τ' = 𝟙 R) :
    P ◁ (D ▷ R) = (σ ▷ (Y ≫ R) ≫ P' ◁ (Y ◁ τ)) ≫ P' ◁ (D ▷ R') ≫
      (P' ◁ (Y' ◁ τ') ≫ σ' ▷ (Y' ≫ R)) := by
  have h₁ : Y ◁ τ ≫ D ▷ R' ≫ Y' ◁ τ' = D ▷ R := by
    rw [whisker_exchange_assoc, ← whiskerLeft_comp, hτ, whiskerLeft_id, Category.comp_id]
  have h₂ : σ ▷ (Y ≫ R) ≫ P' ◁ (D ▷ R) ≫ σ' ▷ (Y' ≫ R) = P ◁ (D ▷ R) := by
    rw [← whisker_exchange_assoc, ← comp_whiskerRight, hσ, id_whiskerRight, Category.comp_id]
  rw [← h₂, ← h₁]
  simp only [whiskerLeft_comp, Category.assoc]

private theorem whisker_eq_of_retract {a b : B} {P' : a ⟶ a} {R' : b ⟶ b} {Y Y' : a ⟶ b}
    (D : Y ⟶ Y') {σ : P' ⟶ 𝟙 a} {σ' : 𝟙 a ⟶ P'} {τ : R' ⟶ 𝟙 b} {τ' : 𝟙 b ⟶ R'}
    (hσ : σ ≫ σ' = 𝟙 P') (hτ : τ ≫ τ' = 𝟙 R') :
    P' ◁ (D ▷ R') = (σ ▷ (Y ≫ R') ≫ (λ_ _).hom ≫ Y ◁ τ ≫ (ρ_ Y).hom) ≫ D ≫
      ((ρ_ Y').inv ≫ Y' ◁ τ' ≫ (λ_ _).inv ≫ σ' ▷ (Y' ≫ R')) := by
  have h₀ : (ρ_ Y).hom ≫ D ≫ (ρ_ Y').inv ≫ Y' ◁ τ' = D ▷ 𝟙 b ≫ Y' ◁ τ' := by
    rw [whiskerRight_id]
    simp only [Category.assoc]
  have h₁ : Y ◁ τ ≫ (ρ_ Y).hom ≫ D ≫ (ρ_ Y').inv ≫ Y' ◁ τ' = D ▷ R' := by
    rw [h₀, whisker_exchange_assoc, ← whiskerLeft_comp, hτ, whiskerLeft_id, Category.comp_id]
  have h₂ : (λ_ (Y ≫ R')).hom ≫ D ▷ R' ≫ (λ_ (Y' ≫ R')).inv = 𝟙 a ◁ (D ▷ R') :=
    (id_whiskerLeft _).symm
  calc P' ◁ (D ▷ R') = σ ▷ (Y ≫ R') ≫ 𝟙 a ◁ (D ▷ R') ≫ σ' ▷ (Y' ≫ R') := by
        rw [← whisker_exchange_assoc, ← comp_whiskerRight, hσ, id_whiskerRight, Category.comp_id]
    _ = _ := by
        rw [← h₂, ← h₁]
        simp only [Category.assoc]

theorem isSandwich_whisker_of_nil {a b : FreeBicategory W} {Xp : a ⟶ a} {Xr : b ⟶ b}
    (hp : normalizeAux .nil Xp = .nil) (hr : normalizeAux .nil Xr = .nil) {Y Y' : a ⟶ b}
    (D : (lift F).map Y ⟶ (lift F).map Y') :
    IsSandwich F (Xp ≫ Y ≫ Xr) (Xp ≫ Y' ≫ Xr) D ((lift F).map Xp ◁ (D ▷ (lift F).map Xr)) := by
  have hid {c : FreeBicategory W} {f g : c ⟶ c} (θ : f ⟶ g) (θ' : g ⟶ f) :
      (lift F).map₂ θ ≫ (lift F).map₂ θ' = 𝟙 _ :=
    ((lift F).map₂_comp _ _).symm.trans ((congrArg (lift F).map₂ (Subsingleton.elim _ _)).trans
      ((lift F).map₂_id _))
  obtain ⟨⟨hσ⟩, ⟨hσ'⟩, ⟨hτ⟩, ⟨hτ'⟩⟩ : Nonempty (Xp ⟶ 𝟙 a) ∧ Nonempty (𝟙 a ⟶ Xp) ∧
      Nonempty (Xr ⟶ 𝟙 b) ∧ Nonempty (𝟙 b ⟶ Xr) :=
    ⟨⟨homOfNormalizeAuxEq hp⟩, ⟨homOfNormalizeAuxEq hp.symm⟩, ⟨homOfNormalizeAuxEq hr⟩,
      ⟨homOfNormalizeAuxEq hr.symm⟩⟩
  have e₁ : (lift F).map₂ (hσ ▷ (Y ≫ Xr) ≫ (λ_ _).hom ≫ Y ◁ hτ ≫ (ρ_ Y).hom) =
      ((lift F).map₂ hσ ▷ ((lift F).map Y ≫ (lift F).map Xr) ≫ (λ_ _).hom ≫
        (lift F).map Y ◁ (lift F).map₂ hτ ≫ (ρ_ _).hom :
          (lift F).map Xp ≫ (lift F).map Y ≫ (lift F).map Xr ⟶ (lift F).map Y) := by
    simp only [PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_whiskerRight]
    rfl
  have e₂ : (lift F).map₂ ((ρ_ Y').inv ≫ Y' ◁ hτ' ≫ (λ_ _).inv ≫ hσ' ▷ (Y' ≫ Xr)) =
      ((ρ_ _).inv ≫ (lift F).map Y' ◁ (lift F).map₂ hτ' ≫ (λ_ _).inv ≫
        (lift F).map₂ hσ' ▷ ((lift F).map Y' ≫ (lift F).map Xr) :
          (lift F).map Y' ⟶ (lift F).map Xp ≫ (lift F).map Y' ≫ (lift F).map Xr) := by
    simp only [PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_whiskerRight]
    rfl
  refine isSandwich_of_eq (hσ ▷ (Y ≫ Xr) ≫ (λ_ _).hom ≫ Y ◁ hτ ≫ (ρ_ Y).hom)
    ((ρ_ Y').inv ≫ Y' ◁ hτ' ≫ (λ_ _).inv ≫ hσ' ▷ (Y' ≫ Xr))
    ((whisker_eq_of_retract D (hid hσ hσ') (hid hτ hτ')).trans ?_)
  rw [e₁, e₂]
  rfl

theorem isSandwich_whisker_congr {W : Type*} [Quiver W] {G : Prefunctor W B}
    {a b c d : FreeBicategory W} {Xp Xp' : a ⟶ b} {Xr Xr' : c ⟶ d} {Y Y' : b ⟶ c}
    (D : (lift G).map Y ⟶ (lift G).map Y') (hp : normalizeAux .nil Xp = normalizeAux .nil Xp')
    (hr : normalizeAux .nil Xr = normalizeAux .nil Xr') :
    IsSandwich G (Xp ≫ Y ≫ Xr) (Xp ≫ Y' ≫ Xr) (X' := Xp' ≫ Y ≫ Xr') (Y' := Xp' ≫ Y' ≫ Xr')
      ((lift G).map Xp' ◁ (D ▷ (lift G).map Xr')) ((lift G).map Xp ◁ (D ▷ (lift G).map Xr)) := by
  have hid {c' d' : FreeBicategory W} {f g : c' ⟶ d'} (θ : f ⟶ g) (θ' : g ⟶ f) :
      (lift G).map₂ θ ≫ (lift G).map₂ θ' = 𝟙 _ :=
    ((lift G).map₂_comp _ _).symm.trans ((congrArg (lift G).map₂ (Subsingleton.elim _ _)).trans
      ((lift G).map₂_id _))
  obtain ⟨⟨σ⟩, ⟨σ'⟩, ⟨τ⟩, ⟨τ'⟩⟩ : Nonempty (Xp ⟶ Xp') ∧ Nonempty (Xp' ⟶ Xp) ∧
      Nonempty (Xr ⟶ Xr') ∧ Nonempty (Xr' ⟶ Xr) :=
    ⟨⟨homOfNormalizeAuxEq hp⟩, ⟨homOfNormalizeAuxEq hp.symm⟩, ⟨homOfNormalizeAuxEq hr⟩,
      ⟨homOfNormalizeAuxEq hr.symm⟩⟩
  have e₁ : (lift G).map₂ (σ ▷ (Y ≫ Xr) ≫ Xp' ◁ (Y ◁ τ)) =
      ((lift G).map₂ σ ▷ ((lift G).map Y ≫ (lift G).map Xr) ≫
        (lift G).map Xp' ◁ ((lift G).map Y ◁ (lift G).map₂ τ) :
          (lift G).map Xp ≫ (lift G).map Y ≫ (lift G).map Xr ⟶
            (lift G).map Xp' ≫ (lift G).map Y ≫ (lift G).map Xr') := by
    simp only [PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_whiskerRight]
    rfl
  have e₂ : (lift G).map₂ (Xp' ◁ (Y' ◁ τ') ≫ σ' ▷ (Y' ≫ Xr)) =
      ((lift G).map Xp' ◁ ((lift G).map Y' ◁ (lift G).map₂ τ') ≫
        (lift G).map₂ σ' ▷ ((lift G).map Y' ≫ (lift G).map Xr) :
          (lift G).map Xp' ≫ (lift G).map Y' ≫ (lift G).map Xr' ⟶
            (lift G).map Xp ≫ (lift G).map Y' ≫ (lift G).map Xr) := by
    simp only [PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_whiskerRight]
    rfl
  refine isSandwich_of_eq (σ ▷ (Y ≫ Xr) ≫ Xp' ◁ (Y ◁ τ)) (Xp' ◁ (Y' ◁ τ') ≫ σ' ▷ (Y' ≫ Xr))
    ((whiskerLeft_whiskerRight_eq_conj D (hid σ σ') (hid τ τ')).trans ?_)
  rw [e₁, e₂]
  rfl

end Whisker

section MapPath

variable {V : Type*} [Quiver V] (F : Prefunctor V B)

theorem pathCompCompIso_hom_mapPath_heq {x y z : V} (p : Quiver.Path x y)
    (q : Quiver.Path y z) :
    (pathCompCompIso (𝟭q B) (F.mapPath p) (F.mapPath q)).hom ≍ (pathCompCompIso F p q).hom := by
  have h₁ : IsStructural (𝟭q B) (pathComp ((𝟭q B) ⋙q FreeBicategory.of)
      ((F.mapPath p).comp (F.mapPath q)))
      (pathComp ((𝟭q B) ⋙q FreeBicategory.of) (F.mapPath p) ≫
        pathComp ((𝟭q B) ⋙q FreeBicategory.of) (F.mapPath q))
      (pathCompCompIso (𝟭q B) (F.mapPath p) (F.mapPath q)).hom :=
    ⟨_, _, _, pathCompCompIso_comp_lift ((𝟭q B) ⋙q FreeBicategory.of) (𝟭q B) _ _⟩
  have h₂ : IsStructural (𝟭q B) (pathComp (F ⋙q FreeBicategory.of) (p.comp q))
      (pathComp (F ⋙q FreeBicategory.of) p ≫ pathComp (F ⋙q FreeBicategory.of) q)
      (pathCompCompIso F p q).hom :=
    ⟨_, _, _, pathCompCompIso_comp_lift (F ⋙q FreeBicategory.of) (𝟭q B) p q⟩
  refine h₁.heq (h₂.congr ?_ ?_)
  · exact ((pathComp_mapPath_comp F _ _).symm.trans (congrArg _ (F.mapPath_comp p q)))
  · exact congrArg₂ (· ≫ ·) (pathComp_mapPath_comp F _ p).symm (pathComp_mapPath_comp F _ q).symm

theorem pathCompCompIso_inv_mapPath_heq {x y z : V} (p : Quiver.Path x y)
    (q : Quiver.Path y z) :
    (pathCompCompIso (𝟭q B) (F.mapPath p) (F.mapPath q)).inv ≍ (pathCompCompIso F p q).inv := by
  have h₁ : IsStructural (𝟭q B) (pathComp ((𝟭q B) ⋙q FreeBicategory.of) (F.mapPath p) ≫
        pathComp ((𝟭q B) ⋙q FreeBicategory.of) (F.mapPath q))
      (pathComp ((𝟭q B) ⋙q FreeBicategory.of) ((F.mapPath p).comp (F.mapPath q)))
      (pathCompCompIso (𝟭q B) (F.mapPath p) (F.mapPath q)).inv :=
    ⟨_, _, _, pathCompCompIso_comp_lift_inv ((𝟭q B) ⋙q FreeBicategory.of) (𝟭q B) _ _⟩
  have h₂ : IsStructural (𝟭q B)
      (pathComp (F ⋙q FreeBicategory.of) p ≫ pathComp (F ⋙q FreeBicategory.of) q)
      (pathComp (F ⋙q FreeBicategory.of) (p.comp q)) (pathCompCompIso F p q).inv :=
    ⟨_, _, _, pathCompCompIso_comp_lift_inv (F ⋙q FreeBicategory.of) (𝟭q B) p q⟩
  refine h₁.heq (h₂.congr ?_ ?_)
  · exact congrArg₂ (· ≫ ·) (pathComp_mapPath_comp F _ p).symm (pathComp_mapPath_comp F _ q).symm
  · exact ((pathComp_mapPath_comp F _ _).symm.trans (congrArg _ (F.mapPath_comp p q)))

theorem pathComp_mapPath_lift {a b : FreeBicategory V} (P : Quiver.Path a b) :
    pathComp (𝟭q B) ((lift F).toPrefunctor.mapPath P) = (lift F).map (pathComp (𝟭q _) P) :=
  (Bicategory.pathComp_mapPath (lift F).toPrefunctor P).trans
    (Bicategory.pathComp_comp_lift (𝟭q _) F P)

theorem isStructural_pathCompCompIso_hom {x y z : FreeBicategory V} (p : Quiver.Path x y)
    (q : Quiver.Path y z) :
    IsStructural F (pathComp (𝟭q _) (p.comp q)) (pathComp (𝟭q _) p ≫ pathComp (𝟭q _) q)
      (pathCompCompIso (𝟭q B) ((lift F).toPrefunctor.mapPath p)
        ((lift F).toPrefunctor.mapPath q)).hom := by
  have h : IsStructural F (pathComp (𝟭q _) (p.comp q)) (pathComp (𝟭q _) p ≫ pathComp (𝟭q _) q)
      (pathCompCompIso (lift F).toPrefunctor p q).hom :=
    ⟨_, _, _, Bicategory.pathCompCompIso_comp_lift (𝟭q _) F p q⟩
  refine IsStructural.of_heq h ((congrArg _ ((lift F).toPrefunctor.mapPath_comp p q).symm).trans
    (Bicategory.pathComp_mapPath _ _)) (congrArg₂ (· ≫ ·) (Bicategory.pathComp_mapPath _ p)
      (Bicategory.pathComp_mapPath _ q)) (pathCompCompIso_hom_mapPath_heq _ p q)

theorem isStructural_pathCompCompIso_inv {x y z : FreeBicategory V} (p : Quiver.Path x y)
    (q : Quiver.Path y z) :
    IsStructural F (pathComp (𝟭q _) p ≫ pathComp (𝟭q _) q) (pathComp (𝟭q _) (p.comp q))
      (pathCompCompIso (𝟭q B) ((lift F).toPrefunctor.mapPath p)
        ((lift F).toPrefunctor.mapPath q)).inv := by
  have h : IsStructural F (pathComp (𝟭q _) p ≫ pathComp (𝟭q _) q) (pathComp (𝟭q _) (p.comp q))
      (pathCompCompIso (lift F).toPrefunctor p q).inv :=
    ⟨_, _, _, Bicategory.pathCompCompIso_comp_lift_inv (𝟭q _) F p q⟩
  refine IsStructural.of_heq h (congrArg₂ (· ≫ ·) (Bicategory.pathComp_mapPath _ p)
      (Bicategory.pathComp_mapPath _ q)) ((congrArg _ ((lift F).toPrefunctor.mapPath_comp p
        q).symm).trans (Bicategory.pathComp_mapPath _ _)) (pathCompCompIso_inv_mapPath_heq _ p q)

theorem eq_of_pathCell_eq_isStructural_left {x y : B} {P : Quiver.Path x y}
    {P₁ : Quiver.Path x x} (h₁ : P₁ = (𝟙 x).toPath) {Q : Quiver.Path x y} (hQ : Q = P₁.comp P)
    {φ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) Q} {a b : FreeBicategory V} {P' : Quiver.Path a b}
    {ψ : pathComp (𝟭q B) ((lift F).toPrefunctor.mapPath P') ⟶
      pathComp (𝟭q B) ((lift F).toPrefunctor.mapPath ((𝟙 a).toPath.comp P'))}
    (hψ : IsStructural F (pathComp (𝟭q _) P') (pathComp (𝟭q _) ((𝟙 a).toPath.comp P')) ψ)
    (h : (⟨x, y, P, Q, φ⟩ : PathCell B) = ⟨_, _, (lift F).toPrefunctor.mapPath P',
      (lift F).toPrefunctor.mapPath ((𝟙 a).toPath.comp P'), ψ⟩) :
    φ = (λ_ (pathComp (𝟭q B) P)).inv ≫
      ((λ_ (𝟙 x)).inv ≫ eqToHom (congrArg (pathComp (𝟭q B)) h₁.symm)) ▷ pathComp (𝟭q B) P ≫
      (pathCompCompIso (𝟭q B) P₁ P).inv ≫ eqToHom (congrArg (pathComp (𝟭q B)) hQ.symm) := by
  subst h₁ hQ
  obtain ⟨hx, hy, hP, -, hφ⟩ := PathCell.mk.inj h
  subst hx hy
  obtain rfl := eq_of_heq hP
  refine eq_of_heq (hφ.trans (hψ.heq ?_))
  exact (isStructural_leftUnitor_inv F _ (pathComp_mapPath_lift F P')).comp
    ((IsStructural.whiskerRight_of_eq ((isStructural_leftUnitor_inv F (𝟙 a) rfl).comp_eqToHom _) _
      (pathComp_mapPath_lift F P')).comp
        ((isStructural_pathCompCompIso_inv F (𝟙 a).toPath P').comp_eqToHom _))

theorem eq_of_pathCell_eq_isStructural_right {x y : B} {P : Quiver.Path x y}
    {P₁ : Quiver.Path y y} (h₁ : P₁ = (𝟙 y).toPath) {Q : Quiver.Path x y} (hQ : Q = P.comp P₁)
    {φ : pathComp (𝟭q B) Q ⟶ pathComp (𝟭q B) P} {a b : FreeBicategory V} {P' : Quiver.Path a b}
    {ψ : pathComp (𝟭q B) ((lift F).toPrefunctor.mapPath (P'.comp (𝟙 b).toPath)) ⟶
      pathComp (𝟭q B) ((lift F).toPrefunctor.mapPath P')}
    (hψ : IsStructural F (pathComp (𝟭q _) (P'.comp (𝟙 b).toPath)) (pathComp (𝟭q _) P') ψ)
    (h : (⟨x, y, Q, P, φ⟩ : PathCell B) =
      ⟨_, _, (lift F).toPrefunctor.mapPath (P'.comp (𝟙 b).toPath),
      (lift F).toPrefunctor.mapPath P', ψ⟩) :
    φ = (eqToHom (congrArg (pathComp (𝟭q B)) hQ) ≫ (pathCompCompIso (𝟭q B) P P₁).hom) ≫
      pathComp (𝟭q B) P ◁ (eqToHom (congrArg (pathComp (𝟭q B)) h₁) ≫ (λ_ (𝟙 y)).hom) ≫
      (ρ_ (pathComp (𝟭q B) P)).hom := by
  subst h₁ hQ
  obtain ⟨hx, hy, -, hP, hφ⟩ := PathCell.mk.inj h
  subst hx hy
  obtain rfl := eq_of_heq hP
  refine eq_of_heq (hφ.trans (hψ.heq ?_))
  exact ((isStructural_pathCompCompIso_hom F P' (𝟙 b).toPath).eqToHom_comp _).comp
    ((IsStructural.whiskerLeft_of_eq ((isStructural_leftUnitor_hom F (𝟙 b) rfl).eqToHom_comp _) _
      (pathComp_mapPath_lift F P')).comp
        (isStructural_rightUnitor_hom F _ (pathComp_mapPath_lift F P')))

end MapPath

end CategoryTheory.FreeBicategory

namespace CategoryTheory.Bicategory

open Quiver

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {V : Type*} [Quiver V] (G : Prefunctor V B)

def PathCell.ofHom {x y : V} (P Q : Path x y) (φ : pathComp G P ⟶ pathComp G Q) : PathCell B :=
  ⟨G.obj x, G.obj y, G.mapPath P, G.mapPath Q,
    eqToHom (pathComp_mapPath G P) ≫ φ ≫ eqToHom (pathComp_mapPath G Q).symm⟩

private theorem conj_comp_conj {C : Type*} [Category C] {X X' Y Y' Z Z' : C} (a : X' = X)
    (b : Y = Y') (b' : Y' = Y) (c : Z = Z') (φ : X ⟶ Y) (χ : Y ⟶ Z) :
    (eqToHom a ≫ φ ≫ eqToHom b) ≫ eqToHom b' ≫ χ ≫ eqToHom c =
      eqToHom a ≫ (φ ≫ χ) ≫ eqToHom c := by
  subst a b c
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem eqToHom_id_eqToHom {C : Type*} [Category C] {X Y : C} (h : X = Y) (h' : Y = X) :
    eqToHom h ≫ 𝟙 Y ≫ eqToHom h' = 𝟙 X := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]

variable {G}

private theorem conj_injective {C : Type*} [Category C] {X X' Y Y' : C} (a : X' = X) (b : Y = Y')
    {φ ψ : X ⟶ Y} (h : eqToHom a ≫ φ ≫ eqToHom b = eqToHom a ≫ ψ ≫ eqToHom b) : φ = ψ := by
  subst a b
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

theorem PathCell.ofHom_injective {x y : V} {P Q : Path x y} {φ ψ : pathComp G P ⟶ pathComp G Q}
    (h : PathCell.ofHom G P Q φ = PathCell.ofHom G P Q ψ) : φ = ψ := by
  obtain ⟨-, -, -, -, hh⟩ := PathCell.mk.inj h
  exact conj_injective _ _ (eq_of_heq hh)

theorem PathCell.ofHom_id {x y : V} (P : Path x y) :
    PathCell.ofHom G P P (𝟙 _) = ⟨G.obj x, G.obj y, G.mapPath P, G.mapPath P, 𝟙 _⟩ :=
  congrArg (PathCell.mk _ _ _ _) (eqToHom_id_eqToHom _ _)

theorem PathCell.ofHom_eqToHom {x y : V} {P Q P' Q' : Path x y} (hP : P = P') (hQ : Q' = Q)
    (φ : pathComp G P' ⟶ pathComp G Q') :
    PathCell.ofHom G P Q (eqToHom (congrArg (pathComp G) hP) ≫ φ ≫
      eqToHom (congrArg (pathComp G) hQ)) = PathCell.ofHom G P' Q' φ := by
  subst hP hQ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem PathCell.ofHom_eqToHom_comp {x y : V} {P P' Q : Path x y} (hP : P = P')
    (φ : pathComp G P' ⟶ pathComp G Q) :
    PathCell.ofHom G P Q (eqToHom (congrArg (pathComp G) hP) ≫ φ) = PathCell.ofHom G P' Q φ := by
  subst hP
  simp only [eqToHom_refl, Category.id_comp]

theorem PathCell.ofHom_congr_heq {x y : V} {P Q P' Q' : Path x y} {φ : pathComp G P ⟶ pathComp G Q}
    {ψ : pathComp G P' ⟶ pathComp G Q'} (hP : P = P') (hQ : Q = Q') (h : φ ≍ ψ) :
    PathCell.ofHom G P Q φ = PathCell.ofHom G P' Q' ψ := by
  subst hP hQ
  rw [eq_of_heq h]

theorem PathCell.ofHom_comp {x y : V} {P Q R : Path x y} (φ : pathComp G P ⟶ pathComp G Q)
    (χ : pathComp G Q ⟶ pathComp G R) :
    (⟨G.obj x, G.obj y, G.mapPath P, G.mapPath R, (PathCell.ofHom G P Q φ).hom ≫
      (PathCell.ofHom G Q R χ).hom⟩ : PathCell B) = PathCell.ofHom G P R (φ ≫ χ) := by
  exact congrArg (PathCell.mk _ _ _ _) (conj_comp_conj _ _ _ _ φ χ)

theorem PathCell.ofHom_whisker {x y z : V} {P Q : Path x y} {P' Q' : Path y z}
    (φ : pathComp G P ⟶ pathComp G Q) (χ : pathComp G P' ⟶ pathComp G Q') :
    (⟨G.obj x, G.obj z, (G.mapPath P).comp (G.mapPath P'), (G.mapPath Q).comp (G.mapPath Q'),
      (pathCompCompIso (𝟭q B) (G.mapPath P) (G.mapPath P')).hom ≫
        ((PathCell.ofHom G P Q φ).hom ▷ pathComp (𝟭q B) (G.mapPath P') ≫
          pathComp (𝟭q B) (G.mapPath Q) ◁ (PathCell.ofHom G P' Q' χ).hom) ≫
        (pathCompCompIso (𝟭q B) (G.mapPath Q) (G.mapPath Q')).inv⟩ : PathCell B) =
      PathCell.ofHom G (P.comp P') (Q.comp Q') ((pathCompCompIso G P P').hom ≫
        (φ ▷ pathComp G P' ≫ pathComp G Q ◁ χ) ≫ (pathCompCompIso G Q Q').inv) := by
  have hP := pathComp_mapPath G P
  have hQ := pathComp_mapPath G Q
  have hP' := pathComp_mapPath G P'
  have hQ' := pathComp_mapPath G Q'
  refine PathCell.ext rfl rfl (heq_of_eq (G.mapPath_comp _ _).symm)
    (heq_of_eq (G.mapPath_comp _ _).symm) ?_
  refine HEq.trans ?_ ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm
  have hX : pathComp (𝟭q B) ((G.mapPath P).comp (G.mapPath P')) = pathComp G (P.comp P') :=
    (congrArg _ (G.mapPath_comp P P').symm).trans (pathComp_mapPath G _)
  have hZ : pathComp (𝟭q B) ((G.mapPath Q).comp (G.mapPath Q')) = pathComp G (Q.comp Q') :=
    (congrArg _ (G.mapPath_comp Q Q').symm).trans (pathComp_mapPath G _)
  have hY := congrArg₂ (· ≫ ·) hP hP'
  have hY₂ := congrArg₂ (· ≫ ·) hQ hP'
  have hW := congrArg₂ (· ≫ ·) hQ hQ'
  refine heq_comp hX hY hZ (FreeBicategory.pathCompCompIso_hom_mapPath_heq G P P') ?_
  refine heq_comp hY hW hZ ?_ (FreeBicategory.pathCompCompIso_inv_mapPath_heq G Q Q')
  refine heq_comp hY hY₂ hW ?_ ?_
  · exact whiskerRight_heq hP hQ hP' ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _))
  · exact whiskerLeft_heq hQ hP' hQ' ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _))

end CategoryTheory.Bicategory

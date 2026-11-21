import Atoms.ForMathlib.CategoryTheory.Category.Cat.Comma
import Atoms.ForMathlib.CategoryTheory.Functor.DiscreteFibration
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

namespace CategoryTheory.Cat

open Limits

universe u

private def intervalArrowObj {C : Type u} (x y : C) : Bool → C
  | false => x
  | true => y

private def intervalArrowMap {C : Type u} [Category.{u} C] {x y : C} (φ : x ⟶ y) :
    (s t : Bool) → s ≤ t → (intervalArrowObj x y s ⟶ intervalArrowObj x y t)
  | false, false, _ => 𝟙 x
  | false, true, _ => φ
  | true, true, _ => 𝟙 y
  | true, false, h => absurd h (by decide)

private def intervalArrow {C : Type u} [Category.{u} C] {x y : C} (φ : x ⟶ y) :
    ULift.{u} Bool ⥤ C where
  obj p := intervalArrowObj x y p.down
  map {p q} f := intervalArrowMap φ p.down q.down (leOfHom (X := ULift.{u} Bool) f)
  map_id p := by rcases p with ⟨_ | _⟩ <;> rfl
  map_comp {p q r} f g := by
    have hf := leOfHom (X := ULift.{u} Bool) f
    have hg := leOfHom (X := ULift.{u} Bool) g
    rcases p with ⟨_ | _⟩ <;> rcases q with ⟨_ | _⟩ <;> rcases r with ⟨_ | _⟩
    all_goals first
      | exact absurd hf (by decide)
      | exact absurd hg (by decide)
      | exact (Category.id_comp _).symm
      | exact (Category.comp_id _).symm

private def intervalArrowHom : (ULift.up false : ULift.{u} Bool) ⟶ ULift.up true :=
  homOfLE (X := ULift.{u} Bool) (show false ≤ true by decide)

private theorem intervalArrow_eq {C : Type u} [Category.{u} C] {x y x' y' : C} (φ : x ⟶ y)
    (ψ : x' ⟶ y') (hx : x = x') (hy : y = y') (h : φ = eqToHom hx ≫ ψ ≫ eqToHom hy.symm) :
    intervalArrow φ = intervalArrow ψ := by
  subst hx hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  subst h
  rfl

private theorem intervalArrow_comp {C D : Type u} [Category.{u} C] [Category.{u} D] {x y : C}
    (φ : x ⟶ y) (F : C ⥤ D) : intervalArrow φ ⋙ F = intervalArrow (F.map φ) := by
  refine CategoryTheory.Functor.ext (fun p => by rcases p with ⟨_ | _⟩ <;> rfl) (fun p q f => ?_)
  have hf := leOfHom (X := ULift.{u} Bool) f
  rcases p with ⟨_ | _⟩ <;> rcases q with ⟨_ | _⟩
  · change F.map (𝟙 x) = eqToHom rfl ≫ 𝟙 (F.obj x) ≫ eqToHom rfl
    simp
  · change F.map φ = eqToHom rfl ≫ F.map φ ≫ eqToHom rfl
    simp
  · exact absurd hf (by decide)
  · change F.map (𝟙 y) = eqToHom rfl ≫ 𝟙 (F.obj y) ≫ eqToHom rfl
    simp

variable {P X Y Z : Cat.{u, u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

theorem obj_eq_of_isPullback (h : IsPullback fst snd f g) (p : P) :
    f.toFunctor.obj (fst.toFunctor.obj p) = g.toFunctor.obj (snd.toFunctor.obj p) :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor h.w) p

theorem obj_ext_of_isPullback (h : IsPullback fst snd f g) {p₁ p₂ : P}
    (h₁ : fst.toFunctor.obj p₁ = fst.toFunctor.obj p₂)
    (h₂ : snd.toFunctor.obj p₁ = snd.toFunctor.obj p₂) : p₁ = p₂ :=
  Types.ext_of_isPullback (h.map Cat.objects) h₁ h₂

theorem exists_obj_of_isPullback (h : IsPullback fst snd f g) (x : X) (y : Y)
    (e : f.toFunctor.obj x = g.toFunctor.obj y) :
    ∃ p : P, fst.toFunctor.obj p = x ∧ snd.toFunctor.obj p = y :=
  Types.exists_of_isPullback (h.map Cat.objects) x y e

theorem hom_ext_of_isPullback (h : IsPullback fst snd f g) {p₁ p₂ : P} {γ₁ γ₂ : p₁ ⟶ p₂}
    (h₁ : fst.toFunctor.map γ₁ = fst.toFunctor.map γ₂)
    (h₂ : snd.toFunctor.map γ₁ = snd.toFunctor.map γ₂) : γ₁ = γ₂ := by
  have e := h.hom_ext (k := (intervalArrow γ₁).toCatHom) (l := (intervalArrow γ₂).toCatHom)
    (Cat.Hom.ext (by
      change intervalArrow γ₁ ⋙ fst.toFunctor = intervalArrow γ₂ ⋙ fst.toFunctor
      rw [intervalArrow_comp, intervalArrow_comp, h₁]))
    (Cat.Hom.ext (by
      change intervalArrow γ₁ ⋙ snd.toFunctor = intervalArrow γ₂ ⋙ snd.toFunctor
      rw [intervalArrow_comp, intervalArrow_comp, h₂]))
  have := Functor.congr_hom (congrArg Cat.Hom.toFunctor e) intervalArrowHom
  change γ₁ = eqToHom rfl ≫ γ₂ ≫ eqToHom rfl at this
  simpa using this

theorem exists_hom_of_isPullback (h : IsPullback fst snd f g) {p₁ p₂ : P}
    (α : fst.toFunctor.obj p₁ ⟶ fst.toFunctor.obj p₂)
    (β : snd.toFunctor.obj p₁ ⟶ snd.toFunctor.obj p₂)
    (e : f.toFunctor.map α =
      eqToHom (obj_eq_of_isPullback h p₁) ≫ g.toFunctor.map β ≫
        eqToHom (obj_eq_of_isPullback h p₂).symm) :
    ∃ γ : p₁ ⟶ p₂, fst.toFunctor.map γ = α ∧ snd.toFunctor.map γ = β := by
  have hw : (intervalArrow α).toCatHom ≫ f = (intervalArrow β).toCatHom ≫ g :=
    Cat.Hom.ext (by
      change intervalArrow α ⋙ f.toFunctor = intervalArrow β ⋙ g.toFunctor
      rw [intervalArrow_comp, intervalArrow_comp]
      exact intervalArrow_eq _ _ (obj_eq_of_isPullback h p₁) (obj_eq_of_isPullback h p₂) e)
  set L := h.lift _ _ hw with hL
  have hf := congrArg Cat.Hom.toFunctor (h.lift_fst _ _ hw)
  have hs := congrArg Cat.Hom.toFunctor (h.lift_snd _ _ hw)
  rw [← hL] at hf hs
  have e₀ : L.toFunctor.obj (ULift.up false) = p₁ := obj_ext_of_isPullback h
    (Functor.congr_obj hf (ULift.up false)) (Functor.congr_obj hs (ULift.up false))
  have e₁ : L.toFunctor.obj (ULift.up true) = p₂ := obj_ext_of_isPullback h
    (Functor.congr_obj hf (ULift.up true)) (Functor.congr_obj hs (ULift.up true))
  refine ⟨eqToHom e₀.symm ≫ L.toFunctor.map intervalArrowHom ≫ eqToHom e₁, ?_, ?_⟩
  · have key : fst.toFunctor.map (L.toFunctor.map intervalArrowHom) =
        eqToHom (congrArg fst.toFunctor.obj e₀) ≫ α ≫
          eqToHom (congrArg fst.toFunctor.obj e₁).symm :=
      Functor.congr_hom hf intervalArrowHom
    simp [key, eqToHom_map]
  · have key : snd.toFunctor.map (L.toFunctor.map intervalArrowHom) =
        eqToHom (congrArg snd.toFunctor.obj e₀) ≫ β ≫
          eqToHom (congrArg snd.toFunctor.obj e₁).symm :=
      Functor.congr_hom hs intervalArrowHom
    simp [key, eqToHom_map]

theorem isPullback_of_elementwise (w : fst ≫ f = snd ≫ g)
    (hobjExt : ∀ {p₁ p₂ : P}, fst.toFunctor.obj p₁ = fst.toFunctor.obj p₂ →
      snd.toFunctor.obj p₁ = snd.toFunctor.obj p₂ → p₁ = p₂)
    (hobj : ∀ (x : X) (y : Y), f.toFunctor.obj x = g.toFunctor.obj y →
      ∃ p : P, fst.toFunctor.obj p = x ∧ snd.toFunctor.obj p = y)
    (hhomExt : ∀ {p₁ p₂ : P} {γ₁ γ₂ : p₁ ⟶ p₂}, fst.toFunctor.map γ₁ = fst.toFunctor.map γ₂ →
      snd.toFunctor.map γ₁ = snd.toFunctor.map γ₂ → γ₁ = γ₂)
    (hhom : ∀ {p₁ p₂ : P} (α : fst.toFunctor.obj p₁ ⟶ fst.toFunctor.obj p₂)
      (β : snd.toFunctor.obj p₁ ⟶ snd.toFunctor.obj p₂),
      f.toFunctor.map α =
        eqToHom (Functor.congr_obj (congrArg Cat.Hom.toFunctor w) p₁) ≫ g.toFunctor.map β ≫
          eqToHom (Functor.congr_obj (congrArg Cat.Hom.toFunctor w) p₂).symm →
      ∃ γ : p₁ ⟶ p₂, fst.toFunctor.map γ = α ∧ snd.toFunctor.map γ = β) :
    IsPullback fst snd f g := by
  have hs : ∀ (s : PullbackCone f g) τ,
      f.toFunctor.obj (s.fst.toFunctor.obj τ) = g.toFunctor.obj (s.snd.toFunctor.obj τ) :=
    fun s τ => Functor.congr_obj (congrArg Cat.Hom.toFunctor s.condition) τ
  let o : ∀ s : PullbackCone f g, s.pt → P := fun s τ => (hobj _ _ (hs s τ)).choose
  have o₁ : ∀ s τ, fst.toFunctor.obj (o s τ) = s.fst.toFunctor.obj τ :=
    fun s τ => (hobj _ _ (hs s τ)).choose_spec.1
  have o₂ : ∀ s τ, snd.toFunctor.obj (o s τ) = s.snd.toFunctor.obj τ :=
    fun s τ => (hobj _ _ (hs s τ)).choose_spec.2
  have hm : ∀ (s : PullbackCone f g) {τ τ' : s.pt} (m : τ ⟶ τ'), ∃ γ : o s τ ⟶ o s τ',
      fst.toFunctor.map γ = eqToHom (o₁ s τ) ≫ s.fst.toFunctor.map m ≫ eqToHom (o₁ s τ').symm ∧
      snd.toFunctor.map γ = eqToHom (o₂ s τ) ≫ s.snd.toFunctor.map m ≫ eqToHom (o₂ s τ').symm := by
    intro s τ τ' m
    refine hhom _ _ ?_
    have := Functor.congr_hom (congrArg Cat.Hom.toFunctor s.condition) m
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at this
    simp [eqToHom_map, this]
  let L : ∀ s : PullbackCone f g, s.pt ⟶ P := fun s => Functor.toCatHom
    { obj := o s
      map := fun m => (hm s m).choose
      map_id := fun τ => hhomExt (by rw [(hm s _).choose_spec.1]; simp)
        (by rw [(hm s _).choose_spec.2]; simp)
      map_comp := fun m m' => hhomExt
        (by
          rw [fst.toFunctor.map_comp, (hm s (m ≫ m')).choose_spec.1, (hm s m).choose_spec.1,
            (hm s m').choose_spec.1]
          simp)
        (by
          rw [snd.toFunctor.map_comp, (hm s (m ≫ m')).choose_spec.2, (hm s m).choose_spec.2,
            (hm s m').choose_spec.2]
          simp) }
  have L₁ : ∀ s, L s ≫ fst = s.fst := fun s =>
    Cat.Hom.ext (CategoryTheory.Functor.ext (o₁ s) (fun _ _ m => (hm s m).choose_spec.1))
  have L₂ : ∀ s, L s ≫ snd = s.snd := fun s =>
    Cat.Hom.ext (CategoryTheory.Functor.ext (o₂ s) (fun _ _ m => (hm s m).choose_spec.2))
  refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w L L₁ L₂ ?_)
  intro s m h₁ h₂
  have e₁ := congrArg Cat.Hom.toFunctor h₁
  have e₂ := congrArg Cat.Hom.toFunctor h₂
  have eo : ∀ τ, m.toFunctor.obj τ = o s τ := fun τ =>
    hobjExt ((Functor.congr_obj e₁ τ).trans (o₁ s τ).symm)
      ((Functor.congr_obj e₂ τ).trans (o₂ s τ).symm)
  refine Cat.Hom.ext (CategoryTheory.Functor.ext eo (fun τ τ' φ => hhomExt ?_ ?_))
  · have := Functor.congr_hom e₁ φ
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at this
    change _ = fst.toFunctor.map (eqToHom _ ≫ (hm s φ).choose ≫ eqToHom _)
    rw [this, Functor.map_comp, Functor.map_comp, (hm s φ).choose_spec.1]
    simp [eqToHom_map]
  · have := Functor.congr_hom e₂ φ
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at this
    change _ = snd.toFunctor.map (eqToHom _ ≫ (hm s φ).choose ≫ eqToHom _)
    rw [this, Functor.map_comp, Functor.map_comp, (hm s φ).choose_spec.2]
    simp [eqToHom_map]

section DiscreteFibration

variable {C C' B' B : Cat.{u, u}} {v' : C' ⟶ C} {q' : C' ⟶ B'} {q : C ⟶ B} {v : B' ⟶ B}

theorem isDiscreteFibration_of_isPullback (h : IsPullback v' q' q v)
    (hv : Functor.IsDiscreteFibration v.toFunctor) : Functor.IsDiscreteFibration v'.toFunctor where
  exists_lift {c'} c g := by
    have hw := Cat.obj_eq_of_isPullback h c'
    obtain ⟨x, φ, ex, hφ⟩ := hv.exists_lift (q.toFunctor.map g ≫ eqToHom hw)
    obtain ⟨p, hp₁, hp₂⟩ := Cat.exists_obj_of_isPullback h c x ex.symm
    obtain ⟨γ, hγ₁, -⟩ := Cat.exists_hom_of_isPullback h (eqToHom hp₁ ≫ g) (eqToHom hp₂ ≫ φ)
      (by simp [hφ, eqToHom_map])
    exact ⟨p, γ, hp₁, hγ₁⟩
  lift_unique {c'} c₁ c₂ f₁ f₂ e H := by
    have sq : ∀ {a b : C'} (f : a ⟶ b), v.toFunctor.map (q'.toFunctor.map f) =
        eqToHom (Cat.obj_eq_of_isPullback h a).symm ≫ q.toFunctor.map (v'.toFunctor.map f) ≫
          eqToHom (Cat.obj_eq_of_isPullback h b) := fun f => by
      have := Functor.congr_hom (congrArg Cat.Hom.toFunctor h.w) f
      simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at this
      simp [this]
    have e₂ : v.toFunctor.obj (q'.toFunctor.obj c₁) = v.toFunctor.obj (q'.toFunctor.obj c₂) :=
      (Cat.obj_eq_of_isPullback h c₁).symm.trans
        ((congrArg q.toFunctor.obj e).trans (Cat.obj_eq_of_isPullback h c₂))
    obtain ⟨e', he'⟩ := hv.lift_unique (q'.toFunctor.map f₁) (q'.toFunctor.map f₂) e₂
      (by simp [sq, H, eqToHom_map])
    obtain rfl : c₁ = c₂ := Cat.obj_ext_of_isPullback h e e'
    refine ⟨rfl, ?_⟩
    simp only [eqToHom_refl, Category.id_comp] at H he' ⊢
    exact Cat.hom_ext_of_isPullback h H he'

theorem isEquivalence_commaSquareFunctor_of_isDiscreteFibration {D D' : Cat.{u, u}}
    {w : D' ⟶ D} {t' : D' ⟶ C'} {t : D ⟶ C} (h : IsPullback w t' t v')
    (hv : Functor.IsDiscreteFibration v'.toFunctor) (c' : C') :
    (commaSquareFunctor w t' t v' h.w c').IsEquivalence := by
  set Φ := commaSquareFunctor w t' t v' h.w c'
  have hw := Cat.obj_eq_of_isPullback h
  have hΦ : ∀ x : CostructuredArrow t'.toFunctor c', (Φ.obj x).hom =
      eqToHom (hw x.left) ≫ v'.toFunctor.map x.hom := fun x => by
    simp [Φ, commaSquareFunctor, CategoryTheory.eqToHom_app]
  have sq : ∀ {a b : D'} (f : a ⟶ b), v'.toFunctor.map (t'.toFunctor.map f) =
      eqToHom (hw a).symm ≫ t.toFunctor.map (w.toFunctor.map f) ≫ eqToHom (hw b) := fun f => by
    have := Functor.congr_hom (congrArg Cat.Hom.toFunctor h.w) f
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at this
    simp [this]
  have faithful : Φ.Faithful := ⟨fun {x y} m₁ m₂ hm => by
    have hl : w.toFunctor.map m₁.left = w.toFunctor.map m₂.left :=
      congrArg CommaMorphism.left hm
    ext
    exact Cat.hom_ext_of_isPullback h hl (hv.map_injective (by rw [sq, sq, hl]))⟩
  have full : Φ.Full := ⟨fun {x y} n => by
    let n' : w.toFunctor.obj x.left ⟶ w.toFunctor.obj y.left := n.left
    have hn : t.toFunctor.map n' ≫ eqToHom (hw y.left) ≫ v'.toFunctor.map y.hom =
        eqToHom (hw x.left) ≫ v'.toFunctor.map x.hom := by
      have := CostructuredArrow.w n
      rw [hΦ, hΦ] at this
      exact this
    obtain ⟨c₁, β₀, e₀, hβ₀⟩ := hv.exists_lift
      (eqToHom (hw x.left).symm ≫ t.toFunctor.map n' ≫ eqToHom (hw y.left))
    obtain ⟨e₁, hβ₁⟩ := hv.lift_unique (β₀ ≫ y.hom) x.hom e₀ (by
      rw [Functor.map_comp, hβ₀]
      simp [hn])
    obtain ⟨m, hm₁, hm₂⟩ := Cat.exists_hom_of_isPullback h n' (eqToHom e₁.symm ≫ β₀)
      (by simp [hβ₀, eqToHom_map])
    refine ⟨CostructuredArrow.homMk m (by rw [hm₂]; simp [hβ₁]), ?_⟩
    ext
    exact hm₁⟩
  have essSurj : Φ.EssSurj := ⟨fun y => by
    obtain ⟨c₁, φ, e, hφ⟩ := hv.exists_lift y.hom
    obtain ⟨d', hd₁, hd₂⟩ := Cat.exists_obj_of_isPullback h y.left c₁ e.symm
    refine ⟨CostructuredArrow.mk (Y := d') (eqToHom hd₂ ≫ φ),
      ⟨CostructuredArrow.isoMk (eqToIso hd₁) ?_⟩⟩
    rw [hΦ]
    change t.toFunctor.map (eqToHom hd₁) ≫ y.hom = _
    simp [hφ, eqToHom_map]⟩
  exact { }

end DiscreteFibration

section CommaComparison

variable {A' A B' B : Cat.{u, u}}

theorem isPullback_mapRightToId (u : A ⟶ B) (v : B' ⟶ B) :
    IsPullback (Comma.mapRightToId u.toFunctor v.toFunctor).toCatHom
      (Comma.snd u.toFunctor v.toFunctor).toCatHom (Comma.snd u.toFunctor (𝟭 B)).toCatHom v := by
  refine Cat.isPullback_of_elementwise rfl ?_ ?_ ?_ ?_
  · intro p₁ p₂ h₁ h₂
    obtain ⟨l₁, r₁, f₁⟩ := p₁
    obtain ⟨l₂, r₂, f₂⟩ := p₂
    change r₁ = r₂ at h₂
    subst h₂
    injection h₁ with hl _ hf
    subst hl
    cases hf
    rfl
  · rintro ⟨l, r, f⟩ y (e : r = v.toFunctor.obj y)
    subst e
    exact ⟨⟨l, y, f⟩, rfl, rfl⟩
  · intro p₁ p₂ γ₁ γ₂ h₁ h₂
    have h : (Comma.mapRightToId u.toFunctor v.toFunctor).map γ₁ =
        (Comma.mapRightToId u.toFunctor v.toFunctor).map γ₂ := h₁
    exact Comma.hom_ext _ _ (congrArg
      (fun m : (Comma.mapRightToId u.toFunctor v.toFunctor).obj p₁ ⟶
        (Comma.mapRightToId u.toFunctor v.toFunctor).obj p₂ => m.left) h) h₂
  · intro p₁ p₂ α β e
    change α.right = eqToHom rfl ≫ v.toFunctor.map β ≫ eqToHom rfl at e
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at e
    refine ⟨⟨α.left, β, ?_⟩, ?_, rfl⟩
    · have := α.w
      change u.toFunctor.map α.left ≫ p₂.hom = p₁.hom ≫ α.right at this
      rw [e] at this
      exact this
    · exact Comma.hom_ext _ _ rfl e.symm

theorem isPullback_ofSquare {w : A' ⟶ A} {u' : A' ⟶ B'} {u : A ⟶ B} {v : B' ⟶ B}
    (h : IsPullback w u' u v) :
    IsPullback w (Comma.ofSquare w.toFunctor u'.toFunctor u.toFunctor v.toFunctor
        (congrArg Cat.Hom.toFunctor h.w)).toCatHom (Comma.idSection u.toFunctor).toCatHom
      (Comma.mapRightToId u.toFunctor v.toFunctor).toCatHom := by
  refine IsPullback.of_bot (show IsPullback w ((Comma.ofSquare w.toFunctor u'.toFunctor
    u.toFunctor v.toFunctor (congrArg Cat.Hom.toFunctor h.w)).toCatHom ≫
    (Comma.snd u.toFunctor v.toFunctor).toCatHom) ((Comma.idSection u.toFunctor).toCatHom ≫
      (Comma.snd u.toFunctor (𝟭 B)).toCatHom) v from h) ?_ (isPullback_mapRightToId u v)
  have e := Cat.obj_eq_of_isPullback h
  have key : ∀ (l : A) (r r' : B) (e : r = r') (f : u.toFunctor.obj l ⟶ r),
      (⟨l, r, f⟩ : Comma u.toFunctor (𝟭 B)) = ⟨l, r', f ≫ eqToHom e⟩ := by
    rintro l r r' rfl f
    simp
  have p : w.toFunctor ⋙ Comma.idSection u.toFunctor =
      Comma.ofSquare w.toFunctor u'.toFunctor u.toFunctor v.toFunctor
        (congrArg Cat.Hom.toFunctor h.w) ⋙ Comma.mapRightToId u.toFunctor v.toFunctor := by
    refine CategoryTheory.Functor.ext (fun a => ?_) (fun a b f => ?_)
    · change (⟨w.toFunctor.obj a, u.toFunctor.obj (w.toFunctor.obj a), 𝟙 _⟩ :
        Comma u.toFunctor (𝟭 B)) = ⟨w.toFunctor.obj a, v.toFunctor.obj (u'.toFunctor.obj a),
          eqToHom (e a)⟩
      rw [key _ _ _ (e a) (𝟙 _), Category.id_comp]
    · apply Comma.hom_ext
      · simp only [Comma.comp_left]
        rw [Comma.eqToHom_left, Comma.eqToHom_left]
        simp only [Comma.idSection, Comma.ofSquare, Comma.mapRightToId, Functor.comp_map]
        erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
      · have := Functor.congr_hom (congrArg Cat.Hom.toFunctor h.w) f
        simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at this
        simp only [Comma.comp_right]
        rw [Comma.eqToHom_right, Comma.eqToHom_right]
        simp [Comma.idSection, Comma.ofSquare, Comma.mapRightToId, this]
  exact Cat.Hom.ext p

end CommaComparison

end CategoryTheory.Cat

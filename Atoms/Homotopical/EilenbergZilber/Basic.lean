import Atoms.ForMathlib.CategoryTheory.Category.ULift
import Atoms.ForMathlib.CategoryTheory.EpiMono
import Atoms.ForMathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Subfunctor.Basic

open CategoryTheory Limits MorphismProperty Opposite

namespace Atoms.Homotopical

universe w v u

section AbsolutePushout

variable {A : Type u} [Category.{v} A]

def IsAbsolutePushout {a b c d : A} (f : a ⟶ b) (g : a ⟶ c) (h : b ⟶ d) (k : c ⟶ d) : Prop :=
  IsPushout (yoneda.map f) (yoneda.map g) (yoneda.map h) (yoneda.map k)

namespace IsAbsolutePushout

variable {a b c d : A} {f : a ⟶ b} {g : a ⟶ c} {h : b ⟶ d} {k : c ⟶ d}

theorem w (sq : IsAbsolutePushout f g h k) : f ≫ h = g ≫ k := by
  have hw := (IsPushout.toCommSq sq).w
  rw [← Functor.map_comp, ← Functor.map_comp] at hw
  exact yoneda.map_injective hw

theorem flip (sq : IsAbsolutePushout f g h k) : IsAbsolutePushout g f k h :=
  IsPushout.flip sq

end IsAbsolutePushout

end AbsolutePushout

section Transport

@[simps!]
private def yonedaIsoWhiskerOfFullyFaithful {D D' : Type*} [Category.{w} D] [Category.{w} D']
    {F : D ⥤ D'} (hF : F.FullyFaithful) :
    (yoneda : D ⥤ _) ≅ F ⋙ yoneda ⋙ (Functor.whiskeringLeft Dᵒᵖ D'ᵒᵖ (Type w)).obj F.op :=
  NatIso.ofComponents
    (fun a ↦ NatIso.ofComponents (fun z ↦ (hF.homEquiv (X := z.unop) (Y := a)).toIso)
      (fun g ↦ by ext; simp [Functor.FullyFaithful.homEquiv]))
    (fun f ↦ by ext; simp [Functor.FullyFaithful.homEquiv])

theorem IsAbsolutePushout.of_map_of_fullyFaithful {D D' : Type*} [Category.{w} D]
    [Category.{w} D'] {F : D ⥤ D'} (hF : F.FullyFaithful) {a b c d : D} {f : a ⟶ b}
    {g : a ⟶ c} {h : b ⟶ d} {k : c ⟶ d}
    (sq : IsAbsolutePushout (F.map f) (F.map g) (F.map h) (F.map k)) :
    IsAbsolutePushout f g h k := by
  let φ := yonedaIsoWhiskerOfFullyFaithful hF
  let W := (Functor.whiskeringLeft Dᵒᵖ D'ᵒᵖ (Type w)).obj F.op
  exact (IsPushout.map W sq).of_iso (φ.app a).symm (φ.app b).symm (φ.app c).symm
    (φ.app d).symm (φ.inv.naturality f) (φ.inv.naturality g) (φ.inv.naturality h)
    (φ.inv.naturality k)

theorem IsAbsolutePushout.comp_iso {D : Type*} [Category.{w} D] {a b c d d' : D} {f : a ⟶ b}
    {g : a ⟶ c} {h : b ⟶ d} {k : c ⟶ d} (sq : IsAbsolutePushout f g h k) (e : d ≅ d') :
    IsAbsolutePushout f g (h ≫ e.hom) (k ≫ e.hom) :=
  IsPushout.of_iso sq (Iso.refl _) (Iso.refl _) (Iso.refl _) (yoneda.mapIso e) (by simp)
    (by simp) (by simp) (by simp)

theorem IsAbsolutePushout.asSmall {A : Type u} [Category.{v} A] {a b c d : A} {f : a ⟶ b}
    {g : a ⟶ c} {h : b ⟶ d} {k : c ⟶ d} (sq : IsAbsolutePushout f g h k) :
    IsAbsolutePushout ((AsSmall.up : A ⥤ AsSmall.{w} A).map f) (AsSmall.up.map g)
      (AsSmall.up.map h) (AsSmall.up.map k) := by
  let Φ : (Aᵒᵖ ⥤ Type v) ⥤ ((AsSmall.{w} A)ᵒᵖ ⥤ Type (max w v u)) :=
    (Functor.whiskeringLeft _ _ _).obj AsSmall.down.op ⋙
      (Functor.whiskeringRight _ _ _).obj uliftFunctor.{max w u, v}
  exact IsPushout.map Φ sq

end Transport

section TrivialAutomorphisms

variable (A : Type u) [Category.{v} A]

class HasTrivialAutomorphisms : Prop where
  subsingleton_aut : ∀ a : A, Subsingleton (a ≅ a)

variable {A}

instance HasTrivialAutomorphisms.subsingleton_iso [HasTrivialAutomorphisms A] (a b : A) :
    Subsingleton (a ≅ b) :=
  ⟨fun e₁ e₂ ↦ by
    have h := congrArg Iso.hom
      ((HasTrivialAutomorphisms.subsingleton_aut a).elim (e₁ ≪≫ e₂.symm) (Iso.refl a))
    ext
    simpa [Iso.comp_inv_eq] using h⟩

instance HasTrivialAutomorphisms.asSmall [HasTrivialAutomorphisms A] :
    HasTrivialAutomorphisms (AsSmall.{w} A) where
  subsingleton_aut a := ⟨fun e₁ e₂ ↦ by
    have h := (HasTrivialAutomorphisms.subsingleton_aut (AsSmall.down.obj a)).elim
      (AsSmall.down.mapIso e₁) (AsSmall.down.mapIso e₂)
    ext
    exact AsSmall.down.map_injective (congrArg Iso.hom h)⟩

end TrivialAutomorphisms

namespace EZCategory

variable {A : Type u} [Category.{v} A]

def IsNondegenerate (X : Aᵒᵖ ⥤ Type w) {a : A} (x : X.obj (op a)) : Prop :=
  ∀ ⦃b : A⦄ (p : a ⟶ b), IsSplitEpi p → (∃ y : X.obj (op b), X.map p.op y = x) → IsIso p

end EZCategory

section Decomposition

variable {A : Type u} [Category.{v} A] {deg : A → ℕ}

theorem exists_isSplitEpi_isNondegenerate_of_deg
    (hle : ∀ ⦃a b : A⦄ (i : a ⟶ b), Mono i → deg a ≤ deg b)
    (hiso : ∀ ⦃a b : A⦄ (i : a ⟶ b), Mono i → deg a = deg b → IsIso i)
    (X : Aᵒᵖ ⥤ Type w) {a : A} (x : X.obj (op a)) :
    ∃ (b : A) (p : a ⟶ b) (y : X.obj (op b)),
      IsSplitEpi p ∧ EZCategory.IsNondegenerate X y ∧ X.map p.op y = x := by
  induction h : deg a using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    by_cases hx : EZCategory.IsNondegenerate X x
    · exact ⟨a, 𝟙 a, x, inferInstance, hx, by simp⟩
    · simp only [EZCategory.IsNondegenerate, not_forall] at hx
      obtain ⟨b, p, hp, ⟨y, hy⟩, hnp⟩ := hx
      obtain ⟨c, q, z, hq, hz, hzy⟩ :=
        ih _ (h ▸ deg_lt_of_isSplitEpi_of_not_isIso hle hiso p hnp) y rfl
      refine ⟨c, p ≫ q, z, inferInstance, hz, ?_⟩
      rw [op_comp, X.map_comp_apply, hzy, hy]

private theorem mono_section_comp_of_isNondegenerate
    (hfac : ∀ ⦃a b : A⦄ (f : a ⟶ b), ∃ (c : A) (p : a ⟶ c) (i : c ⟶ b),
      IsSplitEpi p ∧ Mono i ∧ p ≫ i = f)
    (X : Aᵒᵖ ⥤ Type w) {a b b' : A} {p : a ⟶ b} (f : a ⟶ b') {y : X.obj (op b)}
    {y' : X.obj (op b')} (hy : EZCategory.IsNondegenerate X y) (h : X.map p.op y = X.map f.op y')
    (s : b ⟶ a) (hs : s ≫ p = 𝟙 b) :
    Mono (s ≫ f) ∧ X.map (s ≫ f).op y' = y := by
  have hy' : X.map (s ≫ f).op y' = y := by
    rw [op_comp, X.map_comp_apply, ← h, ← X.map_comp_apply, ← op_comp, hs, op_id,
      X.map_id_apply]
  obtain ⟨c, r, i, hr, hi, hri⟩ := hfac (s ≫ f)
  have : IsIso r := hy r hr ⟨X.map i.op y', by rw [← X.map_comp_apply, ← op_comp, hri, hy']⟩
  refine ⟨?_, hy'⟩
  rw [← hri]
  exact mono_comp r i

private theorem exists_iso_of_isNondegenerate [HasTrivialAutomorphisms A]
    (hle : ∀ ⦃a b : A⦄ (i : a ⟶ b), Mono i → deg a ≤ deg b)
    (hiso : ∀ ⦃a b : A⦄ (i : a ⟶ b), Mono i → deg a = deg b → IsIso i)
    (hfac : ∀ ⦃a b : A⦄ (f : a ⟶ b), ∃ (c : A) (p : a ⟶ c) (i : c ⟶ b),
      IsSplitEpi p ∧ Mono i ∧ p ≫ i = f)
    (hsec : ∀ ⦃a b : A⦄ (p q : a ⟶ b), IsSplitEpi p → IsSplitEpi q →
      (∀ s : b ⟶ a, s ≫ p = 𝟙 b ↔ s ≫ q = 𝟙 b) → p = q)
    (X : Aᵒᵖ ⥤ Type w) {a b b' : A} {p : a ⟶ b} {p' : a ⟶ b'} {y : X.obj (op b)}
    {y' : X.obj (op b')} [IsSplitEpi p] [IsSplitEpi p'] (hy : EZCategory.IsNondegenerate X y)
    (hy' : EZCategory.IsNondegenerate X y') (h : X.map p.op y = X.map p'.op y') :
    ∃ e : b ≅ b', p ≫ e.hom = p' ∧ X.map e.hom.op y' = y := by
  have key : ∀ (s : b ⟶ a), s ≫ p = 𝟙 b → IsIso (s ≫ p') := fun s hs ↦ by
    obtain ⟨hi, -⟩ := mono_section_comp_of_isNondegenerate hfac X p' hy h s hs
    obtain ⟨hi', -⟩ := mono_section_comp_of_isNondegenerate hfac X p hy' h.symm
      (section_ p') (IsSplitEpi.id p')
    exact hiso _ hi (le_antisymm (hle _ hi) (hle _ hi'))
  have key' : ∀ (t : b' ⟶ a), t ≫ p' = 𝟙 b' → IsIso (t ≫ p) := fun t ht ↦ by
    obtain ⟨hi, -⟩ := mono_section_comp_of_isNondegenerate hfac X p hy' h.symm t ht
    obtain ⟨hi', -⟩ := mono_section_comp_of_isNondegenerate hfac X p' hy h
      (section_ p) (IsSplitEpi.id p)
    exact hiso _ hi (le_antisymm (hle _ hi) (hle _ hi'))
  have := key (section_ p) (IsSplitEpi.id p)
  let θ : b ≅ b' := asIso (section_ p ≫ p')
  have hs : ∀ s : b ⟶ a, s ≫ p = 𝟙 b → s ≫ p' = θ.hom := fun s hs ↦ by
    have := key s hs
    exact congrArg Iso.hom (Subsingleton.elim (asIso (s ≫ p')) θ)
  have ht : ∀ t : b' ⟶ a, t ≫ p' = 𝟙 b' → t ≫ p = θ.inv := fun t ht ↦ by
    have := key' t ht
    exact congrArg Iso.hom (Subsingleton.elim (asIso (t ≫ p)) θ.symm)
  have hpθ : p = p' ≫ θ.inv := by
    refine hsec p (p' ≫ θ.inv) inferInstance inferInstance fun s ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [← Category.assoc, hs s h, Iso.hom_inv_id]
    · have h' : (θ.inv ≫ s) ≫ p' = 𝟙 b' := by
        rw [← cancel_mono θ.inv, Category.assoc, Category.assoc, h, Category.id_comp,
          Category.comp_id]
      rw [← cancel_epi θ.inv, ← Category.assoc, ht _ h', Category.comp_id]
  refine ⟨θ, by rw [hpθ, Category.assoc, Iso.inv_hom_id, Category.comp_id], ?_⟩
  exact (mono_section_comp_of_isNondegenerate hfac X p' hy h _ (IsSplitEpi.id p)).2

private theorem exists_absolutePushout_of_isSplitEpi [HasTrivialAutomorphisms A]
    (hle : ∀ ⦃a b : A⦄ (i : a ⟶ b), Mono i → deg a ≤ deg b)
    (hiso : ∀ ⦃a b : A⦄ (i : a ⟶ b), Mono i → deg a = deg b → IsIso i)
    (hfac : ∀ ⦃a b : A⦄ (f : a ⟶ b), ∃ (c : A) (p : a ⟶ c) (i : c ⟶ b),
      IsSplitEpi p ∧ Mono i ∧ p ≫ i = f)
    (hsec : ∀ ⦃a b : A⦄ (p q : a ⟶ b), IsSplitEpi p → IsSplitEpi q →
      (∀ s : b ⟶ a, s ≫ p = 𝟙 b ↔ s ≫ q = 𝟙 b) → p = q)
    {a b c : A} (p : a ⟶ b) (q : a ⟶ c) [IsSplitEpi p] [IsSplitEpi q] :
    ∃ (d : A) (p' : b ⟶ d) (q' : c ⟶ d), IsAbsolutePushout p q p' q' := by
  let P := pushout (yoneda.map p) (yoneda.map q)
  let jb : yoneda.obj b ⟶ P := pushout.inl _ _
  let jc : yoneda.obj c ⟶ P := pushout.inr _ _
  obtain ⟨d, α, k, hα, hk, hαk⟩ := exists_isSplitEpi_isNondegenerate_of_deg hle hiso P
    (yonedaEquiv jb)
  obtain ⟨d', β, k', hβ, hk', hβk'⟩ := exists_isSplitEpi_isNondegenerate_of_deg hle hiso P
    (yonedaEquiv jc)
  have hsq : P.map (p ≫ α).op k = P.map (q ≫ β).op k' := by
    rw [op_comp, P.map_comp_apply, hαk, op_comp, P.map_comp_apply, hβk',
      yonedaEquiv_naturality, yonedaEquiv_naturality, pushout.condition]
  obtain ⟨θ, hθ, hθk⟩ := exists_iso_of_isNondegenerate hle hiso hfac hsec P hk hk' hsq
  let β' := β ≫ θ.inv
  have hw : p ≫ α = q ≫ β' := by
    rw [← cancel_mono θ.hom]
    simp only [β', Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, hθ]
  have hβ'k : P.map β'.op k = yonedaEquiv jc := by
    rw [← hθk, ← P.map_comp_apply, ← op_comp, show β' ≫ θ.hom = β by simp [β'], hβk']
  let K : yoneda.obj d ⟶ P := yonedaEquiv.symm k
  have hαK : yoneda.map α ≫ K = jb := yonedaEquiv.injective (by
    rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, hαk])
  have hβK : yoneda.map β' ≫ K = jc := yonedaEquiv.injective (by
    rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, hβ'k])
  let ℓ : P ⟶ yoneda.obj d := pushout.desc (yoneda.map α) (yoneda.map β')
    (by rw [← Functor.map_comp, ← Functor.map_comp, hw])
  have hℓK : ℓ ≫ K = 𝟙 P := pushout.hom_ext
    (by rw [pushout.inl_desc_assoc, hαK, Category.comp_id])
    (by rw [pushout.inr_desc_assoc, hβK, Category.comp_id])
  have hKℓ : K ≫ ℓ = 𝟙 (yoneda.obj d) := by
    rw [← cancel_epi (yoneda.map α), reassoc_of% hαK, pushout.inl_desc, Category.comp_id]
  let i : yoneda.obj d ≅ P := ⟨K, ℓ, hKℓ, hℓK⟩
  exact ⟨d, α, β', IsPushout.of_iso_pushout
    ⟨by rw [← Functor.map_comp, ← Functor.map_comp, hw]⟩ i hαK hβK⟩

end Decomposition

variable (A : Type u) [Category.{v} A]

class EZCategory where
  deg : A → ℕ
  deg_le_of_mono : ∀ {a b : A} (f : a ⟶ b), Mono f → deg a ≤ deg b
  isIso_of_mono_of_deg_eq : ∀ {a b : A} (f : a ⟶ b), Mono f → deg a = deg b → IsIso f
  exists_factorization : ∀ {a b : A} (f : a ⟶ b),
    ∃ (c : A) (p : a ⟶ c) (i : c ⟶ b), IsSplitEpi p ∧ Mono i ∧ p ≫ i = f
  exists_absolutePushout : ∀ {a b c : A} (p : a ⟶ b) (q : a ⟶ c), IsSplitEpi p → IsSplitEpi q →
    ∃ (d : A) (p' : b ⟶ d) (q' : c ⟶ d), IsAbsolutePushout p q p' q'

namespace EZCategory

variable {A}

@[instance_reducible]
def ofCollapseInclusion [HasTrivialAutomorphisms A] (deg : A → ℕ)
    (collapses inclusions : MorphismProperty A) [collapses.RespectsIso] [inclusions.RespectsIso]
    (hcollapses : collapses ≤ MorphismProperty.splitEpimorphisms A)
    (hinclusions : inclusions ≤ MorphismProperty.monomorphisms A)
    (hle : ∀ ⦃a b : A⦄ (i : a ⟶ b), inclusions i → deg a ≤ deg b)
    (hiso : ∀ ⦃a b : A⦄ (i : a ⟶ b), inclusions i → deg a = deg b → IsIso i)
    (hfac : ∀ ⦃a b : A⦄ (f : a ⟶ b), ∃ (c : A) (p : a ⟶ c) (i : c ⟶ b),
      collapses p ∧ inclusions i ∧ p ≫ i = f)
    (hsec : ∀ ⦃a b : A⦄ (p q : a ⟶ b), collapses p → collapses q →
      (∀ s : b ⟶ a, s ≫ p = 𝟙 b ↔ s ≫ q = 𝟙 b) → p = q) :
    EZCategory A :=
  have hmono : ∀ ⦃a b : A⦄ (f : a ⟶ b), Mono f → inclusions f := fun _ _ f _ ↦ by
    obtain ⟨_, p, i, hp, hi, rfl⟩ := hfac f
    have : IsSplitEpi p := hcollapses p hp
    have : Mono p := mono_of_mono p i
    have := isIso_of_mono_of_isSplitEpi p
    exact RespectsIso.precomp inclusions p i hi
  have hsplit : ∀ ⦃a b : A⦄ (f : a ⟶ b), IsSplitEpi f → collapses f := fun _ _ f hf ↦ by
    obtain ⟨_, p, i, hp, hi, rfl⟩ := hfac f
    have : IsSplitEpi (p ≫ i) := hf
    have : IsSplitEpi i := isSplitEpi_of_comp p i
    have : Mono i := hinclusions i hi
    have := isIso_of_mono_of_isSplitEpi i
    exact RespectsIso.postcomp collapses i p hp
  have hfac' : ∀ ⦃a b : A⦄ (f : a ⟶ b), ∃ (c : A) (p : a ⟶ c) (i : c ⟶ b),
      IsSplitEpi p ∧ Mono i ∧ p ≫ i = f := fun _ _ f ↦ by
    obtain ⟨c, p, i, hp, hi, h⟩ := hfac f
    exact ⟨c, p, i, hcollapses p hp, hinclusions i hi, h⟩
  have hle' : ∀ ⦃a b : A⦄ (i : a ⟶ b), Mono i → deg a ≤ deg b := fun _ _ i hi ↦
    hle i (hmono i hi)
  have hiso' : ∀ ⦃a b : A⦄ (i : a ⟶ b), Mono i → deg a = deg b → IsIso i := fun _ _ i hi ↦
    hiso i (hmono i hi)
  { deg
    deg_le_of_mono := fun f hf ↦ hle' f hf
    isIso_of_mono_of_deg_eq := fun f hf ↦ hiso' f hf
    exists_factorization := fun f ↦ hfac' f
    exists_absolutePushout := fun p q hp hq ↦
      have := hp
      have := hq
      exists_absolutePushout_of_isSplitEpi hle' hiso' hfac'
        (fun _ _ p q hp hq ↦ hsec p q (hsplit p hp) (hsplit q hq)) p q }

variable [EZCategory A]

theorem deg_le_of_isSplitEpi {a b : A} (p : a ⟶ b) [IsSplitEpi p] : deg b ≤ deg a :=
  deg_le_of_mono (section_ p) inferInstance

theorem deg_eq_of_iso {a b : A} (e : a ≅ b) : deg a = deg b :=
  le_antisymm (deg_le_of_mono e.hom inferInstance) (deg_le_of_mono e.inv inferInstance)

theorem isIso_of_isSplitEpi_of_deg_eq {a b : A} (p : a ⟶ b) [IsSplitEpi p]
    (h : deg b = deg a) : IsIso p := by
  have := isIso_of_mono_of_deg_eq (section_ p) inferInstance h
  exact IsIso.of_epi_section p

def boundary (a : A) : Subfunctor (yoneda.obj a) where
  obj b := {f : b.unop ⟶ a | ¬ IsSplitEpi f}
  map g _ hf hsplit := hf (@isSplitEpi_of_comp _ _ _ _ _ g.unop _ hsplit)

def uliftBoundary (a : A) : Subfunctor (uliftYoneda.{w}.obj a) where
  obj _ := {f | ¬ IsSplitEpi f.down}
  map g _ hf hsplit := hf (@isSplitEpi_of_comp _ _ _ _ _ g.unop _ hsplit)

omit [EZCategory A] in
theorem mem_uliftBoundary_iff {a : A} {b : Aᵒᵖ} (f : (uliftYoneda.{w}.obj a).obj b) :
    f ∈ (uliftBoundary.{w} a).obj b ↔ ¬ IsSplitEpi f.down :=
  Iff.rfl

omit [EZCategory A] in
def uliftBoundaryIsoBoundary (a : A) : (uliftBoundary.{v} a).toFunctor ≅ (boundary a).toFunctor :=
  NatIso.ofComponents (fun _ ↦
    { hom := ↾fun f ↦ ⟨f.1.down, f.2⟩
      inv := ↾fun f ↦ ⟨⟨f.1⟩, f.2⟩ }) fun _ ↦ rfl

@[instance_reducible]
def ofEquivalence {D D' : Type*} [Category.{v} D] [Category.{v} D'] [EZCategory D']
    (e : D ≌ D') : EZCategory D where
  deg a := deg (e.functor.obj a)
  deg_le_of_mono f _ := deg_le_of_mono (e.functor.map f) inferInstance
  isIso_of_mono_of_deg_eq f _ h := by
    have := isIso_of_mono_of_deg_eq (e.functor.map f) inferInstance h
    exact isIso_of_fully_faithful e.functor f
  exists_factorization f := by
    obtain ⟨c, p, i, hp, hi, hpi⟩ := exists_factorization (e.functor.map f)
    let ε := e.counitIso.app c
    refine ⟨e.inverse.obj c, e.functor.preimage (p ≫ ε.inv), e.functor.preimage (ε.hom ≫ i),
      (e.functor.isSplitEpi_iff _).1 ?_, ?_, ?_⟩
    · rw [Functor.map_preimage]
      exact inferInstance
    · refine e.functor.mono_of_mono_map ?_
      rw [Functor.map_preimage]
      exact mono_comp _ _
    · exact e.functor.map_injective (by simp [hpi])
  exists_absolutePushout p q hp hq := by
    obtain ⟨d, p', q', sq⟩ := exists_absolutePushout (e.functor.map p)
      (e.functor.map q) inferInstance inferInstance
    let ε := e.counitIso.app d
    refine ⟨e.inverse.obj d, e.functor.preimage (p' ≫ ε.inv), e.functor.preimage (q' ≫ ε.inv),
      IsAbsolutePushout.of_map_of_fullyFaithful e.fullyFaithfulFunctor ?_⟩
    rw [Functor.map_preimage, Functor.map_preimage]
    exact sq.comp_iso ε.symm

instance asSmall : EZCategory (AsSmall.{w} A) where
  deg a := deg (AsSmall.down.obj a)
  deg_le_of_mono f _ := deg_le_of_mono (AsSmall.down.map f) inferInstance
  isIso_of_mono_of_deg_eq f _ h := by
    have := isIso_of_mono_of_deg_eq (AsSmall.down.map f) inferInstance h
    exact isIso_of_fully_faithful AsSmall.down f
  exists_factorization f := by
    obtain ⟨c, p, i, hp, hi, hpi⟩ := exists_factorization (AsSmall.down.map f)
    let F : A ⥤ AsSmall.{w} A := AsSmall.up
    have hp' : IsSplitEpi (F.map p) := inferInstance
    have hi' : Mono (F.map i) := inferInstance
    exact ⟨F.obj c, F.map p, F.map i, hp', hi', AsSmall.down.map_injective hpi⟩
  exists_absolutePushout p q _ _ := by
    obtain ⟨d, p', q', sq⟩ := exists_absolutePushout (AsSmall.down.map p)
      (AsSmall.down.map q) inferInstance inferInstance
    exact ⟨AsSmall.up.obj d, AsSmall.up.map p', AsSmall.up.map q', sq.asSmall⟩

end EZCategory

end Atoms.Homotopical

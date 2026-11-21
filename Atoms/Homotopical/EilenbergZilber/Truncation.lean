import Atoms.ForMathlib.CategoryTheory.Subfunctor.Basic
import Atoms.Homotopical.EilenbergZilber.Normal

open CategoryTheory Limits Opposite

namespace Atoms.Homotopical.EZCategory

universe w v u

section General

variable {A : Type u} [Category.{v} A] [EZCategory A]

variable (A) in
def degLE (n : ℕ) : ObjectProperty A := fun a ↦ deg a ≤ n

theorem degLE_iff {n : ℕ} {a : A} : degLE A n a ↔ deg a ≤ n :=
  Iff.rfl

theorem exists_isSplitEpi_forall_isIso (a : A) :
    ∃ (b : A) (p : a ⟶ b), IsSplitEpi p ∧ ∀ (c : A) (q : b ⟶ c), IsSplitEpi q → IsIso q := by
  obtain ⟨b, p, y, hp, hy, -⟩ :=
    exists_isNondegenerate ((Functor.const Aᵒᵖ).obj PUnit.{1}) a PUnit.unit
  exact ⟨b, p, hp, fun c q hq ↦ hy q hq ⟨PUnit.unit, rfl⟩⟩

theorem deg_le_of_forall_isIso {b b' : A}
    (hb : ∀ (c : A) (q : b ⟶ c), IsSplitEpi q → IsIso q) (f : b ⟶ b') : deg b ≤ deg b' := by
  obtain ⟨c, r, i, hr, hi, -⟩ := exists_factorization f
  have : IsIso r := hb c r hr
  exact (deg_eq_of_iso (asIso r)).trans_le (deg_le_of_mono i hi)

theorem tfae_exists_hom_deg_le (n : ℕ) (a : A) :
    List.TFAE [∃ (b : A) (_ : a ⟶ b), deg b ≤ n,
      ∃ (b : A) (p : a ⟶ b), IsSplitEpi p ∧ deg b ≤ n,
      ∀ (b : A) (p : a ⟶ b), IsSplitEpi p →
        (∀ (c : A) (q : b ⟶ c), IsSplitEpi q → IsIso q) → deg b ≤ n] := by
  tfae_have 1 → 3 := by
    rintro ⟨b', f, hb'⟩ b p hp hb
    exact (deg_le_of_forall_isIso hb (section_ p ≫ f)).trans hb'
  tfae_have 3 → 2 := fun h ↦ by
    obtain ⟨b, p, hp, hb⟩ := exists_isSplitEpi_forall_isIso a
    exact ⟨b, p, hp, h b p hp hb⟩
  tfae_have 2 → 1 := fun ⟨b, p, _, hb⟩ ↦ ⟨b, p, hb⟩
  tfae_finish

theorem deg_le_of_map_mem_skeletonSubfunctor {n : ℕ} {X : Aᵒᵖ ⥤ Type w} {a b : A} (p : a ⟶ b)
    [IsSplitEpi p] {y : X.obj (op b)} (hy : IsNondegenerate X y)
    (h : X.map p.op y ∈ (skeletonSubfunctor n X).obj (op a)) : deg b ≤ n :=
  (mem_skeletonSubfunctor_iff_of_isNondegenerate hy).1
    ((map_mem_skeletonSubfunctor_iff_of_isSplitEpi p y).1 h)

theorem skeletonSubfunctor_eq_preimage {X Y : Aᵒᵖ ⥤ Type w} (φ : X ⟶ Y) [Mono φ] (n : ℕ) :
    skeletonSubfunctor n X = (skeletonSubfunctor n Y).preimage φ := by
  refine le_antisymm (fun a x hx ↦ range_skeletonSubfunctor_ι_comp_le φ _ ⟨⟨x, hx⟩, rfl⟩) ?_
  rintro ⟨a⟩ x hx
  obtain ⟨b, p, z, hp, hz, rfl⟩ := exists_isNondegenerate X a x
  replace hx : Y.map p.op (φ.app (op b) z) ∈ (skeletonSubfunctor n Y).obj (op a) := by
    rw [← NatTrans.naturality_apply]
    exact hx
  exact map_mem_skeletonSubfunctor p z (deg_le_of_map_mem_skeletonSubfunctor p
    (hz.app_of_injective φ (injective_of_mono (φ.app _))) hx)

theorem tfae_skeletonSubfunctor_eq_top (n : ℕ) (X : Aᵒᵖ ⥤ Type w) :
    List.TFAE [skeletonSubfunctor n X = ⊤,
      ∀ ⦃a : A⦄ (x : X.obj (op a)), IsNondegenerate X x → deg a ≤ n,
      ∀ ⦃a : A⦄ (x : X.obj (op a)), ∃ (b : A) (p : a ⟶ b) (y : X.obj (op b)),
        IsSplitEpi p ∧ deg b ≤ n ∧ X.map p.op y = x] := by
  tfae_have 1 → 2 := fun h a x hx ↦ by
    refine (mem_skeletonSubfunctor_iff_of_isNondegenerate hx).1 ?_
    rw [h]
    exact Set.mem_univ x
  tfae_have 2 → 3 := fun h a x ↦ by
    obtain ⟨b, p, y, hp, hy, rfl⟩ := exists_isNondegenerate X a x
    exact ⟨b, p, y, hp, h y hy, rfl⟩
  tfae_have 3 → 1 := fun h ↦ by
    refine eq_top_iff.2 ?_
    rintro ⟨a⟩ x -
    obtain ⟨b, p, y, -, hb, rfl⟩ := h x
    exact map_mem_skeletonSubfunctor p y hb
  tfae_finish

theorem mono_of_injective_of_skeletonSubfunctor_eq_top {X Y : Aᵒᵖ ⥤ Type w} (φ : X ⟶ Y) (n : ℕ)
    (hX : skeletonSubfunctor n X = ⊤)
    (hφ : ∀ a : A, deg a ≤ n → Function.Injective (φ.app (op a))) : Mono φ := by
  have hdeg := ((tfae_skeletonSubfunctor_eq_top n X).out 0 1).1 hX
  refine (NatTrans.mono_iff_mono_app φ).2 fun ⟨a⟩ ↦ (mono_iff_injective _).2 fun u₀ u₁ h ↦ ?_
  obtain ⟨b₀, p₀, v₀, hp₀, hv₀, rfl⟩ := exists_isNondegenerate X a u₀
  obtain ⟨b₁, p₁, v₁, hp₁, hv₁, rfl⟩ := exists_isNondegenerate X a u₁
  have hinj₀ := hφ b₀ (hdeg v₀ hv₀)
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply] at h
  obtain ⟨e, ⟨he, hev⟩, -⟩ := existsUnique_iso_of_isNondegenerate Y p₀ p₁ _ _ hp₀
    (hv₀.app_of_injective φ hinj₀) hp₁ (hv₁.app_of_injective φ (hφ b₁ (hdeg v₁ hv₁))) h
  rw [← NatTrans.naturality_apply] at hev
  rw [← hinj₀ hev, ← Functor.map_comp_apply, ← op_comp, he]

end General

section Truncation

variable {A : Type v} [SmallCategory A] [EZCategory A]

abbrev truncation (n : ℕ) :
    (Aᵒᵖ ⥤ Type (max w v)) ⥤ ((degLE A n).FullSubcategoryᵒᵖ ⥤ Type (max w v)) :=
  (Functor.whiskeringLeft _ _ _).obj (degLE A n).ι.op

variable {n : ℕ}

private theorem exists_eq_map_lanUnit_app (F : (degLE A n).FullSubcategoryᵒᵖ ⥤ Type (max w v))
    {a : A} (x : ((degLE A n).ι.op.lan.obj F).obj (op a)) :
    ∃ (b : (degLE A n).FullSubcategory) (f : a ⟶ b.obj) (y : F.obj (op b)),
      ((degLE A n).ι.op.lan.obj F).map f.op
        ((((degLE A n).ι.op.lanUnit).app F).app (op b) y) = x := by
  obtain ⟨g, y, rfl⟩ := Types.jointly_surjective_of_isColimit
    ((degLE A n).ι.op.isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := F) _
      ((degLE A n).ι.op.lanUnit.app F) (op a)) x
  exact ⟨g.left.unop, g.hom.unop, y, rfl⟩

private theorem counit_app_app_map_lanUnit_app_app (X : Aᵒᵖ ⥤ Type (max w v))
    (b : (degLE A n).FullSubcategory) {a : A} (f : a ⟶ b.obj) (y : X.obj (op b.obj)) :
    (((degLE A n).ι.op.lanAdjunction (Type (max w v))).counit.app X).app (op a)
      (((degLE A n).ι.op.lan.obj ((truncation.{w} n).obj X)).map f.op
        ((((degLE A n).ι.op.lanUnit).app ((truncation.{w} n).obj X)).app (op b) y)) =
      X.map f.op y :=
  (NatTrans.naturality_apply _ f.op _).trans (congrArg (X.map f.op) (ConcreteCategory.congr_hom
    ((degLE A n).ι.op.lanUnit_app_app_lanAdjunction_counit_app_app X (op b)) y))

private theorem injective_lanAdjunction_counit_app_app (X : Aᵒᵖ ⥤ Type (max w v)) {a : A}
    (ha : deg a ≤ n) :
    Function.Injective
      ((((degLE A n).ι.op.lanAdjunction (Type (max w v))).counit.app X).app (op a)) := by
  have h : (((degLE A n).ι.op.lanAdjunction (Type (max w v))).counit.app X).app (op a) =
      inv ((((degLE A n).ι.op.lanUnit).app ((truncation.{w} n).obj X)).app
        (op ⟨a, degLE_iff.2 ha⟩)) :=
    IsIso.eq_inv_of_hom_inv_id
      ((degLE A n).ι.op.lanUnit_app_app_lanAdjunction_counit_app_app X (op ⟨a, degLE_iff.2 ha⟩))
  rw [h]
  exact injective_of_mono _

theorem skeletonSubfunctor_lan_obj_eq_top (F : (degLE A n).FullSubcategoryᵒᵖ ⥤ Type (max w v)) :
    skeletonSubfunctor n ((degLE A n).ι.op.lan.obj F) = ⊤ := by
  refine eq_top_iff.2 ?_
  rintro ⟨a⟩ x -
  obtain ⟨b, f, y, rfl⟩ := exists_eq_map_lanUnit_app F x
  exact map_mem_skeletonSubfunctor f _ (degLE_iff.1 b.property)

variable (n) in
theorem range_lanAdjunction_counit_app (X : Aᵒᵖ ⥤ Type (max w v)) :
    Subfunctor.range (((degLE A n).ι.op.lanAdjunction (Type (max w v))).counit.app X) =
      skeletonSubfunctor n X := by
  refine le_antisymm ?_ ?_
  · rintro ⟨a⟩ _ ⟨x, rfl⟩
    obtain ⟨b, f, y, rfl⟩ := exists_eq_map_lanUnit_app _ x
    exact ⟨b.obj, f, y, degLE_iff.1 b.property, (counit_app_app_map_lanUnit_app_app X b f y).symm⟩
  · rintro ⟨a⟩ _ ⟨b, f, y, hb, rfl⟩
    refine ⟨((degLE A n).ι.op.lan.obj ((truncation.{w} n).obj X)).map f.op
      ((((degLE A n).ι.op.lanUnit).app ((truncation.{w} n).obj X)).app
        (op ⟨b, degLE_iff.2 hb⟩) y), counit_app_app_map_lanUnit_app_app X ⟨b, degLE_iff.2 hb⟩ f y⟩

variable (n) in
instance mono_lanAdjunction_counit_app (X : Aᵒᵖ ⥤ Type (max w v)) :
    Mono (((degLE A n).ι.op.lanAdjunction (Type (max w v))).counit.app X) :=
  mono_of_injective_of_skeletonSubfunctor_eq_top _ n (skeletonSubfunctor_lan_obj_eq_top _)
    fun _ ha ↦ injective_lanAdjunction_counit_app_app X ha

variable (n) in
noncomputable def lanTruncationIsoSkeleton (X : Aᵒᵖ ⥤ Type (max w v)) :
    ((degLE A n).ι.op.lan).obj ((truncation.{w} n).obj X) ≅ (skeletonSubfunctor n X).toFunctor :=
  asIso (Subfunctor.toRange (((degLE A n).ι.op.lanAdjunction (Type (max w v))).counit.app X)) ≪≫
    Subfunctor.isoOfEq (range_lanAdjunction_counit_app n X)

variable (n) in
@[reassoc (attr := simp)]
theorem lanTruncationIsoSkeleton_hom_ι (X : Aᵒᵖ ⥤ Type (max w v)) :
    (lanTruncationIsoSkeleton n X).hom ≫ (skeletonSubfunctor n X).ι =
      ((degLE A n).ι.op.lanAdjunction (Type (max w v))).counit.app X :=
  rfl

end Truncation

end Atoms.Homotopical.EZCategory

import Atoms.Molecule.Construction.Suspension
import Atoms.Molecule.RegularComplex.Basic

universe u

open CategoryTheory Order Set Topology

namespace Atoms.Molecule.OGP

open SuspCarrier

variable {P Q : OGP.{u}}

def suspMap (f : P → Q) : suspension P → suspension Q
  | pole α => pole α
  | susp x => susp (f x)

@[simp] theorem suspMap_pole (f : P → Q) (α : Bool) : suspMap f (pole α) = pole α := rfl

@[simp] theorem suspMap_susp (f : P → Q) (x : P) : suspMap f (susp x) = susp (f x) := rfl

theorem monotone_suspMap {f : P → Q} (hf : Monotone f) : Monotone (suspMap f) := by
  rintro (α | x) (β | y) h
  · exact h
  · exact pole_le_susp α (f y)
  · exact absurd h (not_susp_le_pole x β)
  · exact susp_le_susp.2 (hf (susp_le_susp.1 h))

theorem injective_suspMap {f : P → Q} (hf : Function.Injective f) :
    Function.Injective (suspMap f) := by
  rintro (α | x) (β | y) h
  · exact congrArg pole (pole.inj h)
  · simp at h
  · simp at h
  · exact congrArg susp (hf (susp.inj h))

theorem isClosedMap_suspMap {f : P → Q} (hf : IsClosedMap f) : IsClosedMap (suspMap f) := by
  refine IsUpperSet.isClosedMap_iff_fibration.2 ?_
  have hf' := IsUpperSet.isClosedMap_iff_fibration.1 hf
  rintro (α | x) (β | y) h
  · exact ⟨pole β, h, rfl⟩
  · exact absurd h (not_susp_le_pole y α)
  · exact ⟨pole β, pole_le_susp β x, rfl⟩
  · obtain ⟨x', hx', rfl⟩ := hf' (susp_le_susp.1 h)
    exact ⟨susp x', susp_le_susp.2 hx', rfl⟩

theorem isRDC_suspension (hP : IsRDC P) : IsRDC (suspension P) := by
  intro w
  cases w with
  | pole α => exact .point _ (isMin_pole α)
  | susp x =>
    rw [← susp_Iic]
    exact isMoleculeIn_susp (hP x)

private theorem coe_Iic_pole (R : OGP.{u}) (α : Bool) :
    ((LowerSet.Iic (pole α : suspension R) : LowerSet (suspension R)) : Set (suspension R)) =
      {pole α} := by
  ext w
  cases w <;> simp

theorem finalOn_susp {f : P → Q} {V : LowerSet P} {W : LowerSet Q} (h : FinalOn f V W) :
    FinalOn (suspMap f) V.susp W.susp := by
  refine ⟨fun w hw => ?_, fun y hy => ?_⟩
  · cases w with
    | pole α => exact pole_mem_susp W α
    | susp x => exact susp_mem_susp.2 (h.1 (susp_mem_susp.1 hw))
  · cases y with
    | pole β =>
      have hp : IsLeast ((V.susp : Set (suspension P)) ∩ suspMap f ⁻¹' Ici (pole β)) (pole β) :=
        ⟨⟨pole_mem_susp V β, by simp⟩, fun c hc => by
          cases c with
          | pole γ => exact hc.2
          | susp x => exact pole_le_susp β x⟩
      exact ⟨⟨pole β, hp.1⟩, IsUpperSet.isPreconnected_of_isLeast hp⟩
    | susp y =>
      have he : (V.susp : Set (suspension P)) ∩ suspMap f ⁻¹' Ici (susp y) =
          susp '' ((V : Set P) ∩ f ⁻¹' Ici y) := by
        ext w
        cases w <;> simp
      rw [he]
      exact (h.2 y (susp_mem_susp.1 hy)).image susp
        (IsUpperSet.monotone_iff_continuous.1 fun _ _ hxy => susp_le_susp.2 hxy).continuousOn

theorem isMap_suspMap (hP : IsRDC P) {f : P → Q} (hf : IsMap f) : IsMap (suspMap f) := by
  refine ⟨isClosedMap_suspMap hf.isClosedMap, fun w n α => ?_⟩
  cases w with
  | pole β =>
    have h0 (R : OGP.{u}) (γ : Bool) : krullDim (LowerSet.Iic (pole γ : suspension R)) ≤ n := by
      rw [LowerSet.krullDim_Iic, grade_pole]
      exact_mod_cast Nat.zero_le n
    rw [boundary_eq_self (h0 P β), suspMap_pole, boundary_eq_self (h0 Q β), coe_Iic_pole,
      coe_Iic_pole]
    exact finalOn_singleton (suspMap f) (pole β)
  | susp x =>
    rw [suspMap_susp, ← susp_Iic, ← susp_Iic]
    cases n with
    | zero =>
      rw [boundary_susp_zero ⟨x, le_rfl⟩ α, boundary_susp_zero ⟨f x, le_rfl⟩ α, coe_Iic_pole,
        coe_Iic_pole]
      exact finalOn_singleton (suspMap f) (pole α)
    | succ m =>
      rw [boundary_susp_succ ((hP x).boundary m α).nonempty, boundary_susp_succ (by
        rw [← hf.image_boundary x m α]
        exact ((hP x).boundary m α).nonempty.image f)]
      exact finalOn_susp (hf.finalOn x m α)

theorem functor_isFibered_suspMap {f : P → Q} (hf : Monotone f) [hf.functor.IsFibered] :
    (monotone_suspMap hf).functor.IsFibered := by
  refine (Monotone.functor_isFibered_iff _).2 ?_
  rintro (α | x) (β | y) h
  · exact ⟨pole β, h, rfl, fun _ hz _ => hz.trans (pole_le_pole.2 (pole_le_pole.1 h).symm)⟩
  · exact absurd h (not_susp_le_pole y α)
  · refine ⟨pole β, pole_le_susp β x, rfl, fun z _ hz => ?_⟩
    cases z with
    | pole γ => exact hz
    | susp w => exact absurd hz (not_susp_le_pole (f w) β)
  · obtain ⟨y', hy'x, hy'y, hmax⟩ := Monotone.exists_lift hf (susp_le_susp.1 h)
    refine ⟨susp y', susp_le_susp.2 hy'x, by rw [suspMap_susp, hy'y], fun z hz hzy => ?_⟩
    cases z with
    | pole γ => exact pole_le_susp γ y'
    | susp z => exact susp_le_susp.2 (hmax z (susp_le_susp.1 hz) (susp_le_susp.1 hzy))

theorem isMorphism_suspMap {f : P → Q} (hf : IsMorphism f) : IsMorphism (suspMap f) := by
  refine ⟨fun w α => ?_⟩
  cases w with
  | pole β =>
    rw [suspMap_pole, faces_suspension_pole, faces_suspension_pole]
    exact bijOn_empty _
  | susp x =>
    have hmin : IsMin (f x) ↔ IsMin x := by
      rw [← grade_eq_zero_iff, ← grade_eq_zero_iff, hf.grade_eq]
    refine ⟨fun y hy => ?_, fun y hy z hz hyz => ?_, fun v hv => ?_⟩
    · cases y with
      | pole β =>
        obtain ⟨hx, rfl⟩ := pole_mem_faces_suspension.1 hy
        exact pole_mem_faces_suspension.2 ⟨hmin.2 hx, rfl⟩
      | susp y =>
        exact susp_mem_faces_suspension.2
          ((hf.bijOn_faces x α).mapsTo (susp_mem_faces_suspension.1 hy))
    · cases y with
      | pole β =>
        cases z with
        | pole γ => exact congrArg pole (pole.inj hyz)
        | susp z => simp at hyz
      | susp y =>
        cases z with
        | pole γ => simp at hyz
        | susp z =>
          exact congrArg susp ((hf.bijOn_faces x α).injOn (susp_mem_faces_suspension.1 hy)
            (susp_mem_faces_suspension.1 hz) (susp.inj hyz))
    · cases v with
      | pole β =>
        obtain ⟨hx, hβ⟩ := pole_mem_faces_suspension.1 hv
        exact ⟨pole β, pole_mem_faces_suspension.2 ⟨hmin.1 hx, hβ⟩, rfl⟩
      | susp v =>
        obtain ⟨y, hy, rfl⟩ := (hf.bijOn_faces x α).surjOn (susp_mem_faces_suspension.1 hv)
        exact ⟨susp y, susp_mem_faces_suspension.2 hy, rfl⟩

def suspension.map (f : P ⟶ Q) : suspension P ⟶ suspension Q :=
  ConcreteCategory.ofHom ⟨suspMap f, isMorphism_suspMap (isMorphism f)⟩

@[simp] theorem suspension.map_apply (f : P ⟶ Q) (w : suspension P) :
    suspension.map f w = suspMap f w :=
  rfl

instance (f : P ⟶ Q) [IsInclusion f] : IsInclusion (suspension.map f) :=
  ⟨injective_suspMap (IsInclusion.injective (f := f))⟩

section Functoriality

variable {R : OGP.{u}}

theorem suspMap_id : suspMap (fun x : P => x) = fun w => w := by
  funext w
  cases w <;> rfl

theorem suspMap_comp (f : P → Q) (g : Q → R) :
    suspMap (fun x => g (f x)) = fun w => suspMap g (suspMap f w) := by
  funext w
  cases w <;> rfl

theorem surjective_suspMap {f : P → Q} (hf : Function.Surjective f) :
    Function.Surjective (suspMap f) := by
  rintro (α | y)
  · exact ⟨pole α, rfl⟩
  · obtain ⟨x, rfl⟩ := hf y
    exact ⟨susp x, rfl⟩

def suspension.mapIso (e : P ≅ Q) : suspension P ≅ suspension Q where
  hom := suspension.map e.hom
  inv := suspension.map e.inv
  hom_inv_id := by
    ext (α | x)
    · rfl
    · exact congrArg susp (e.hom_inv_id_apply x)
  inv_hom_id := by
    ext (α | x)
    · rfl
    · exact congrArg susp (e.inv_hom_id_apply x)

@[simp] theorem suspension.mapIso_hom_apply (e : P ≅ Q) (w : suspension P) :
    (suspension.mapIso e).hom w = suspMap e.hom w :=
  rfl

def SuspCarrier.desusp {X : Type u} : (w : SuspCarrier X) → (∀ α, w ≠ pole α) → X
  | pole α, h => (h α rfl).elim
  | susp x, _ => x

@[simp] theorem SuspCarrier.susp_desusp {X : Type u} (w : SuspCarrier X) (h : ∀ α, w ≠ pole α) :
    susp (w.desusp h) = w := by
  cases w with
  | pole α => exact (h α rfl).elim
  | susp x => rfl

theorem isMorphism_of_isMorphism_suspMap {f : P → Q} (hf : IsMorphism (suspMap f)) :
    IsMorphism f := by
  refine ⟨fun x α => ?_⟩
  have hb := hf.bijOn_faces (susp x) α
  refine ⟨fun y hy => susp_mem_faces_suspension.1
      (hb.mapsTo (susp_mem_faces_suspension.2 hy)), fun y hy z hz hyz => susp.inj
      (hb.injOn (susp_mem_faces_suspension.2 hy) (susp_mem_faces_suspension.2 hz)
        (congrArg susp hyz)), fun v hv => ?_⟩
  obtain ⟨w, hw, hwv⟩ := hb.surjOn (susp_mem_faces_suspension.2 hv)
  cases w with
  | pole β => exact nomatch hwv
  | susp y => exact ⟨y, susp_mem_faces_suspension.1 hw, susp.inj hwv⟩

theorem suspension.apply_susp_ne_pole (g : suspension P ⟶ suspension Q) (x : P) (α : Bool) :
    g (susp x) ≠ pole α := fun h => by
  have hg := (isMorphism g).grade_eq (susp x)
  rw [h, grade_pole, grade_susp] at hg
  exact Nat.succ_ne_zero _ hg.symm

def suspension.desuspFun (g : suspension P ⟶ suspension Q) (x : P) : Q :=
  (g (susp x)).desusp (suspension.apply_susp_ne_pole g x)

@[simp] theorem suspension.susp_desuspFun (g : suspension P ⟶ suspension Q) (x : P) :
    susp (suspension.desuspFun g x) = g (susp x) :=
  SuspCarrier.susp_desusp _ _

theorem suspension.apply_pole [Nonempty P] (g : suspension P ⟶ suspension Q) (α : Bool) :
    g (pole α) = pole α := by
  obtain ⟨x₀⟩ := ‹Nonempty P›
  obtain ⟨x, -, hx⟩ := exists_minimal_le_of_wellFoundedLT (fun _ : P => True) x₀ trivial
  have hf := ((isMorphism g).bijOn_faces (susp x) α).mapsTo
    (pole_mem_faces_suspension.2 ⟨fun c hc => hx.2 trivial hc, rfl⟩)
  obtain ⟨β, hβ⟩ : ∃ β, g (pole α) = pole β := by
    have hg := (isMorphism g).grade_eq (pole α)
    revert hg
    rcases g (pole α) with β | z
    · exact fun _ => ⟨β, rfl⟩
    · simp
  rw [hβ, ← suspension.susp_desuspFun] at hf
  rw [hβ, (pole_mem_faces_suspension.1 hf).2]

theorem suspension.suspMap_desuspFun [Nonempty P] (g : suspension P ⟶ suspension Q)
    (w : suspension P) : suspMap (suspension.desuspFun g) w = g w := by
  cases w with
  | pole α => exact (suspension.apply_pole g α).symm
  | susp x => exact suspension.susp_desuspFun g x

def suspension.desuspHom [Nonempty P] (g : suspension P ⟶ suspension Q) : P ⟶ Q :=
  ConcreteCategory.ofHom ⟨suspension.desuspFun g, isMorphism_of_isMorphism_suspMap
    (by simpa only [← funext (suspension.suspMap_desuspFun g)] using isMorphism g)⟩

@[simp] theorem suspension.desuspHom_apply [Nonempty P] (g : suspension P ⟶ suspension Q)
    (x : P) : suspension.desuspHom g x = suspension.desuspFun g x :=
  rfl

theorem suspension.map_desuspHom [Nonempty P] (g : suspension P ⟶ suspension Q) :
    suspension.map (suspension.desuspHom g) = g :=
  ConcreteCategory.hom_ext _ _ (suspension.suspMap_desuspFun g)

def suspension.desuspIso [Nonempty P] (φ : suspension P ≅ suspension Q) : P ≅ Q :=
  haveI : Nonempty Q := ‹Nonempty P›.map (suspension.desuspFun φ.hom)
  { hom := suspension.desuspHom φ.hom
    inv := suspension.desuspHom φ.inv
    hom_inv_id := ConcreteCategory.hom_ext _ _ fun x => susp.inj (by
      simp only [CategoryTheory.comp_apply, suspension.desuspHom_apply,
        suspension.susp_desuspFun, CategoryTheory.Iso.hom_inv_id_apply, CategoryTheory.id_apply])
    inv_hom_id := ConcreteCategory.hom_ext _ _ fun x => susp.inj (by
      simp only [CategoryTheory.comp_apply, suspension.desuspHom_apply,
        suspension.susp_desuspFun, CategoryTheory.Iso.inv_hom_id_apply,
        CategoryTheory.id_apply]) }

theorem suspension.mapIso_desuspIso [Nonempty P] (φ : suspension P ≅ suspension Q) :
    suspension.mapIso (suspension.desuspIso φ) = φ :=
  CategoryTheory.Iso.ext (suspension.map_desuspHom φ.hom)

private theorem faces_point (α : Bool) (x : point.{u}) : point.{u}.faces α x = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h => (isMin_point x).not_lt h.1.lt

def suspension.poleIncl (P : OGP.{u}) (α : Bool) : point.{u} ⟶ suspension P :=
  ConcreteCategory.ofHom ⟨fun _ => pole α, ⟨fun x β => by
    rw [faces_point, faces_suspension_pole]
    exact Set.bijOn_empty _⟩⟩

@[simp] theorem suspension.poleIncl_apply (P : OGP.{u}) (α : Bool) (x : point.{u}) :
    suspension.poleIncl P α x = pole α :=
  rfl

instance (P : OGP.{u}) (α : Bool) : IsInclusion (suspension.poleIncl P α) :=
  ⟨fun _ _ _ => Subsingleton.elim (α := PUnit) _ _⟩

end Functoriality

@[simps obj_toOGP]
def RDCpxDown.suspensionFunctor : RDCpxDown.{u} ⥤ RDCpxDown.{u} where
  obj P := ⟨suspension P.toOGP, isRDC_suspension P.isRDC⟩
  map {P _} f := ConcreteCategory.ofHom
    ⟨suspMap (ConcreteCategory.hom f), isMap_suspMap P.isRDC (ConcreteCategory.hom f).isMap⟩
  map_id P := ConcreteCategory.hom_ext _ _ fun w => by
    cases w <;> rfl
  map_comp f g := ConcreteCategory.hom_ext _ _ fun w => by
    cases w <;> rfl

@[simp] theorem RDCpxDown.suspensionFunctor_map_apply {P Q : RDCpxDown.{u}} (f : P ⟶ Q)
    (w : suspension P.toOGP) :
    ConcreteCategory.hom (suspensionFunctor.map f) w = suspMap (ConcreteCategory.hom f) w :=
  rfl

abbrev RDCpx.suspensionFunctor : RDCpx.{u} ⥤ RDCpx.{u} :=
  RDCpxDown.suspensionFunctor.mapWideSubcategory fun _ _ f (hf : cartesian f) =>
    haveI : (ConcreteCategory.hom f).isMap.monotone.functor.IsFibered := hf
    functor_isFibered_suspMap (ConcreteCategory.hom f).isMap.monotone

theorem map_suspension_map_susp (f : P ⟶ Q) (U : LowerSet P) :
    map (suspension.map f) U.susp = (map f U).susp := by
  refine SetLike.ext fun w => ?_
  cases w with
  | pole α => exact iff_of_true ⟨pole α, pole_mem_susp U α, rfl⟩ (pole_mem_susp _ α)
  | susp y =>
    rw [susp_mem_susp, mem_map, mem_map]
    constructor
    · rintro ⟨w, hw, hwy⟩
      cases w with
      | pole α =>
        rw [suspension.map_apply, suspMap_pole] at hwy
        cases hwy
      | susp x =>
        rw [suspension.map_apply, suspMap_susp] at hwy
        exact ⟨x, susp_mem_susp.1 hw, susp.inj hwy⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨susp x, susp_mem_susp.2 hx, suspMap_susp _ x⟩

theorem nonempty_suspension_restrict_iso (U : LowerSet P) :
    Nonempty (suspension (P.restrict U) ≅ (suspension P).restrict U.susp) := by
  obtain ⟨e, -⟩ := exists_iso_restrict (suspension.map (incl U))
    (by rw [← susp_top, map_suspension_map_susp, map_incl_top])
  exact ⟨e⟩

end Atoms.Molecule.OGP

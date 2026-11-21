import Atoms.ForMathlib.CategoryTheory.Functor.OpenImmersion
import Atoms.TestCategory.CubeTest
import Atoms.TestCategory.TestFunctor

open CategoryTheory Limits Opposite

namespace Atoms.TestCategory

universe u

namespace FunctorialPrecylinder

variable {A : Type u} [SmallCategory A] (P : FunctorialPrecylinder A) (i : A ⥤ Cat.{u, u})

structure IsSeparatingFor : Prop where
  isOpenImmersion (a : A) : (i.map ((P.ι false).app a)).toFunctor.IsOpenImmersion
  notMem_range_one (a : A) (x : i.obj a) :
    (i.map ((P.ι true).app a)).toFunctor.obj x ∉
      Set.range (i.map ((P.ι false).app a)).toFunctor.obj
  map_notMem {a a' : A} (α : a ⟶ a') (y : i.obj (P.I.obj a))
    (hy : y ∉ Set.range (i.map ((P.ι false).app a)).toFunctor.obj) :
    (i.map (P.I.map α)).toFunctor.obj y ∉ Set.range (i.map ((P.ι false).app a')).toFunctor.obj

theorem IsSeparatingFor.over {P : FunctorialPrecylinder A} {i : A ⥤ Cat.{u, u}}
    (hP : P.IsSeparatingFor i) (σ : P.Augmentation) (a : A) :
    (P.over σ a).IsSeparatingFor (Over.forget a ⋙ i) where
  isOpenImmersion b := hP.isOpenImmersion b.left
  notMem_range_one b := hP.notMem_range_one b.left
  map_notMem α := hP.map_notMem α.left

variable {P i} (hP : P.IsSeparatingFor i) (C : Cat.{u, u}) [HasTerminal C]

private noncomputable def glue (a : A) (v : i.obj a ⥤ C) : i.obj (P.I.obj a) ⥤ C :=
  (hP.isOpenImmersion a).extend v terminalIsTerminal

private theorem glue_map {a a' : A} (α : a ⟶ a') (v : i.obj a ⥤ C) (v' : i.obj a' ⥤ C)
    (h : (i.map α).toFunctor ⋙ v' = v) :
    (i.map (P.I.map α)).toFunctor ⋙ glue hP C a' v' = glue hP C a v := by
  refine (hP.isOpenImmersion a).eq_extend _ _ _ ?_ fun x hx =>
    (hP.isOpenImmersion a').extend_obj_of_notMem _ terminalIsTerminal (hP.map_notMem α x hx)
  have e : (i.map ((P.ι false).app a)).toFunctor ⋙ (i.map (P.I.map α)).toFunctor =
      (i.map α).toFunctor ⋙ (i.map ((P.ι false).app a')).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← Cat.Hom.comp_toFunctor, ← i.map_comp, ← i.map_comp,
      ← (P.ι false).naturality, Functor.id_map]
  rw [← Functor.assoc, e, Functor.assoc, glue, (hP.isOpenImmersion a').comp_extend]
  exact h

private theorem map_ι_true_glue (a : A) (v : i.obj a ⥤ C) :
    (i.map ((P.ι true).app a)).toFunctor ⋙ glue hP C a v =
      (Functor.const (i.obj a)).obj (⊤_ C) := by
  have h : ∀ x, ((i.map ((P.ι true).app a)).toFunctor ⋙ glue hP C a v).obj x = ⊤_ C :=
    fun x => (hP.isOpenImmersion a).extend_obj_of_notMem _ terminalIsTerminal
      (hP.notMem_range_one a x)
  refine CategoryTheory.Functor.ext h fun x y f => ?_
  rw [← cancel_mono (eqToHom (h y))]
  exact terminal.hom_ext _ _

private noncomputable def cylElements :
    ((i.nerve C).Elements)ᵒᵖ ⥤ ((i.nerve C).Elements)ᵒᵖ where
  obj p := op ⟨op (P.I.obj (unop p.unop.1)), glue hP C (unop p.unop.1) p.unop.2⟩
  map f := CategoryOfElements.opHomMk (P.I.map f.unop.1.unop) (glue_map hP C _ _ _ f.unop.2)
  map_id _ := CategoryOfElements.op_hom_ext (P.I.map_id _)
  map_comp _ _ := CategoryOfElements.op_hom_ext (P.I.map_comp _ _)

private noncomputable def cylElementsι₀ : 𝟭 _ ⟶ cylElements hP C where
  app p := CategoryOfElements.opHomMk ((P.ι false).app (unop p.unop.1))
    ((hP.isOpenImmersion _).comp_extend _ _)
  naturality _ _ f := CategoryOfElements.op_hom_ext ((P.ι false).naturality f.unop.1.unop)

private noncomputable def constElements : A ⥤ ((i.nerve C).Elements)ᵒᵖ where
  obj a := op ⟨op a, (Functor.const (i.obj a)).obj (⊤_ C)⟩
  map α := CategoryOfElements.opHomMk α rfl

private noncomputable def cylElementsι₁ :
    (CategoryOfElements.π (i.nerve C)).leftOp ⋙ constElements C ⟶ cylElements hP C where
  app p := CategoryOfElements.opHomMk ((P.ι true).app (unop p.unop.1)) (map_ι_true_glue hP C _ _)
  naturality _ _ f := CategoryOfElements.op_hom_ext ((P.ι true).naturality f.unop.1.unop)

end FunctorialPrecylinder

namespace BasicLocalizer

variable (𝒲 : BasicLocalizer.{u}) {A : Type u} [SmallCategory A] {i : A ⥤ Cat.{u, u}}

theorem wPsh_terminal_from_nerve (P : FunctorialPrecylinder A) (hP : P.IsSeparatingFor i)
    (C : Cat.{u, u}) [HasTerminal C] : 𝒲.wPsh A (terminal.from (i.nerve C)) := by
  let r := (CategoryOfElements.π (i.nerve C)).leftOp
  let j := FunctorialPrecylinder.constElements (A := A) (i := i) C
  have hD : 𝒲.W (FunctorialPrecylinder.cylElements hP C).toCatHom :=
    (𝒲.W_iff_of_natTrans (u := 𝟙 (Cat.of _))
      (v := (FunctorialPrecylinder.cylElements hP C).toCatHom)
      (FunctorialPrecylinder.cylElementsι₀ hP C)).1 (𝒲.W.id_mem _)
  have hrj : 𝒲.W (r ⋙ j).toCatHom :=
    (𝒲.W_iff_of_natTrans (u := (r ⋙ j).toCatHom)
      (v := (FunctorialPrecylinder.cylElements hP C).toCatHom)
      (FunctorialPrecylinder.cylElementsι₁ hP C)).2 hD
  have hr : 𝒲.W r.toCatHom := 𝒲.W.of_retract (f := r.toCatHom) (g := (r ⋙ j).toCatHom)
    { i := Arrow.homMk (𝟙 _) j.toCatHom (by rfl)
      r := Arrow.homMk (𝟙 _) r.toCatHom (by rfl)
      retract := by rfl } hrj
  exact 𝒲.W.of_postcomp _ (elementsTerminalHom A) (𝒲.W_elementsTerminalHom A) hr

theorem isLocalTestFunctor_of_isSeparatingFor [∀ a, HasTerminal (i.obj a)]
    (P : FunctorialPrecylinder A) (σ : P.Augmentation) (hP : P.IsSeparatingFor i) :
    𝒲.IsLocalTestFunctor i :=
  (𝒲.isLocalTestFunctor_iff i).2 fun C _ a =>
    have : HasTerminal (Cat.of (Over a)) := Over.mkIdTerminal.hasTerminal
    (𝒲.pshAspherical_over_iff a _).1
      ((𝒲.pshAspherical_iff_wPsh_terminal_from (Over a) (𝒲.terminal_aspherical (Cat.of (Over a)))
        _).2 (𝒲.wPsh_terminal_from_nerve (P.over σ a) (hP.over σ a) C))

end BasicLocalizer

namespace Cube

def toCatMap {m n : Cube.{u}} (f : m ⟶ n) :
    ULift.{u} (Fin m.down → Bool) ⥤ ULift.{u} (Fin n.down → Bool) :=
  Monotone.functor (f := fun x => ⟨Cube.toFun f x.down⟩) fun _ _ h => Cube.toFun_monotone f h

def toCat : Cube.{u} ⥤ Cat.{u, u} where
  obj n := Cat.of (ULift.{u} (Fin n.down → Bool))
  map f := (toCatMap f).toCatHom
  map_id _ := Cat.Hom.ext (CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ _ => rfl)
  map_comp f g := Cat.Hom.ext (CategoryTheory.Functor.ext
    (fun x => congrArg ULift.up (congrFun (toFun_comp f g) x.down)) fun _ _ _ => rfl)

instance (n : Cube.{u}) : HasTerminal (Cube.toCat.obj n) :=
  IsTerminal.hasTerminal (C := Cube.toCat.obj n)
    (X := (⟨fun _ => true⟩ : ULift.{u} (Fin n.down → Bool)))
    (IsTerminal.ofUniqueHom (fun _ => homOfLE (X := ULift.{u} (Fin n.down → Bool))
      fun _ => Bool.le_true _) fun _ _ => Subsingleton.elim (α := @Quiver.Hom
        (ULift.{u} (Fin n.down → Bool)) _ _ _) _ _)

theorem mem_range_toCat_map_face_false_iff (n : Cube.{u})
    (y : ULift.{u} (Fin (n.down + 1) → Bool)) :
    y ∈ Set.range (Cube.toCat.map (face false n)).toFunctor.obj ↔ y.down 0 = false := by
  refine ⟨fun ⟨x, hx⟩ => hx ▸ rfl, fun h => ⟨⟨fun j => y.down j.succ⟩, ?_⟩⟩
  exact congrArg ULift.up (funext fun j => Fin.cases h.symm (fun _ => rfl) j)

theorem isSeparatingFor_toCat : Cube.precylinder.{u}.IsSeparatingFor Cube.toCat where
  isOpenImmersion n :=
    { full := ⟨fun {x y} f => ⟨homOfLE (X := ULift.{u} (Fin n.down → Bool))
        fun j => leOfHom (X := ULift.{u} (Fin (n.down + 1) → Bool)) f j.succ, rfl⟩⟩
      faithful := ⟨fun {_ _} f g _ => by
        rcases f with ⟨⟨_⟩⟩
        rcases g with ⟨⟨_⟩⟩
        rfl⟩
      injective_obj := fun x x' h =>
        congrArg ULift.up (funext fun j => congrFun (congrArg ULift.down h) j.succ)
      mem_range_of_hom := fun f => (mem_range_toCat_map_face_false_iff n _).2
        (Bool.eq_false_of_le_false (leOfHom (X := ULift.{u} (Fin (n.down + 1) → Bool)) f 0)) }
  notMem_range_one n x h :=
    Bool.noConfusion ((mem_range_toCat_map_face_false_iff n _).1 h : true = false)
  map_notMem {a a'} α y hy h := hy ((mem_range_toCat_map_face_false_iff a y).2
    ((mem_range_toCat_map_face_false_iff a' _).1 h))

end Cube

theorem BasicLocalizer.isTestFunctor_cubeToCat (𝒲 : BasicLocalizer.{u}) :
    𝒲.IsTestFunctor Cube.toCat.{u} :=
  (𝒲.isLocalTestFunctor_of_isSeparatingFor Cube.precylinder Cube.augmentation
    Cube.isSeparatingFor_toCat).isTestFunctor (𝒲.terminal_aspherical (Cat.of Cube.{u}))

end Atoms.TestCategory

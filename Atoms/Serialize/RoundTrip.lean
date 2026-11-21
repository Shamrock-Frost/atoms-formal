import Atoms.Serialize.Codec
import Atoms.Serialize.ToDocument
import Atoms.Molecule.Construction.Basic

open Atoms.Molecule (OGP)

namespace Atoms.Serialize

namespace Document

def pointDoc : Document := ofOGP (OGP.point.{0})

def globe1Doc : Document := ofOGP (OGP.globe.{0} 1)

def globe2Doc : Document := ofOGP (OGP.globe.{0} 2)

def simplex2Doc : Document := ofOGP (OGP.simplex.{0} 2)

def squareDoc : Document := ofOGP (OGP.grayProduct (OGP.globe.{0} 1) (OGP.globe.{0} 1))

def decoratedDoc : Document :=
  { globe1Doc with
    labels := some [["x".toList, "y".toList], ["e".toList]]
    layout := some [("scale".toList, Json.num ⟨15, 1⟩)]
    extra := [("provenance".toList, Json.str "drawn".toList)] }

theorem pointDoc_valid : pointDoc.Valid := ofOGP_valid _

theorem globe1Doc_valid : globe1Doc.Valid := ofOGP_valid _

theorem globe2Doc_valid : globe2Doc.Valid := ofOGP_valid _

theorem simplex2Doc_valid : simplex2Doc.Valid := ofOGP_valid _

theorem squareDoc_valid : squareDoc.Valid := ofOGP_valid _

theorem decoratedDoc_valid : decoratedDoc.Valid := by decide +kernel

theorem parse_print_pointDoc : parse pointDoc.print = some pointDoc := by decide +kernel

theorem parse_print_globe1Doc : parse globe1Doc.print = some globe1Doc := by decide +kernel

theorem parse_print_globe2Doc : parse globe2Doc.print = some globe2Doc := by decide +kernel

theorem parse_print_simplex2Doc : parse simplex2Doc.print = some simplex2Doc := by decide +kernel

theorem parse_print_squareDoc : parse squareDoc.print = some squareDoc := by decide +kernel

theorem parse_print_decoratedDoc : parse decoratedDoc.print = some decoratedDoc := by decide +kernel

def specExampleText : List Char :=
  [ '{', '\n', ' ', ' ', '\"', 'f', 'o', 'r', 'm', 'a', 't', '\"', ':', ' ', '\"', 'o', 'g',
    'p', 'o', 's', 'e', 't', '\"', ',', '\n', ' ', ' ', '\"', 'v', 'e', 'r', 's', 'i', 'o',
    'n', '\"', ':', ' ', '1', ',', '\n', ' ', ' ', '\"', 'f', 'a', 'c', 'e', 's', '\"', ':',
    ' ', '[', '\n', ' ', ' ', ' ', ' ', '[', ' ', '{', '\"', '-', '\"', ':', ' ', '[', ']',
    ',', ' ', '\"', '+', '\"', ':', ' ', '[', ']', '}', ',', ' ', '{', '\"', '-', '\"', ':',
    ' ', '[', ']', ',', ' ', '\"', '+', '\"', ':', ' ', '[', ']', '}', ' ', ']', ',', '\n',
    ' ', ' ', ' ', ' ', '[', ' ', '{', '\"', '-', '\"', ':', ' ', '[', '0', ']', ',', ' ',
    '\"', '+', '\"', ':', ' ', '[', '1', ']', '}', ' ', ']', '\n', ' ', ' ', ']', '\n', '}']

example : parse specExampleText = some globe1Doc := by decide +kernel

example : ofOGP (pointDoc.toOGP pointDoc_valid.1.2) = pointDoc := by decide +kernel

example : ofOGP (globe1Doc.toOGP globe1Doc_valid.1.2) = globe1Doc := by decide +kernel

example : ofOGP (globe2Doc.toOGP globe2Doc_valid.1.2) = globe2Doc := by decide +kernel

example : ofOGP (simplex2Doc.toOGP simplex2Doc_valid.1.2) = simplex2Doc := by decide +kernel

example : ofOGP (squareDoc.toOGP squareDoc_valid.1.2) = squareDoc := by decide +kernel

example :
    ofOGP (decoratedDoc.toOGP decoratedDoc_valid.1.2) decoratedDoc.labels
      decoratedDoc.layout decoratedDoc.extra = decoratedDoc := by decide +kernel

end Document

end Atoms.Serialize

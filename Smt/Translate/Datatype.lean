/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Smt.Translate
import Smt.Util

namespace Smt.Translate.Datatype

open Translator Term Lean

/-- Translate a constructor of a simple inductive type.
The inductive type itself is marked as a dependency so that the query builder will emit a
`declare-datatypes` command for it. Constructor arguments are translated recursively. -/
@[smt_translate] def translateConstructor : Translator := fun e => do
  let some (v, args) ← Lean.Meta.constructorApp? e | return none
  let env ← getEnv
  let inductName := v.induct
  if Util.smtConsts.contains inductName.toString then return none
  let some (.inductInfo iVal) := env.find? inductName | return none
  if iVal.numIndices != 0 then return none
  if args.size != v.numParams + v.numFields then return none
  modify fun st => { st with depConstants := st.depConstants.insert inductName }
  if v.numParams > 0 && v.numFields == 0 then
    let paramArgs := args.extract 0 v.numParams
    let translatedParams ← paramArgs.mapM applyTranslators!
    let inductSort := translatedParams.foldl appT (symbolT inductName.toString)
    return some <| literalT s!"(as {Term.quoteSymbol v.name.toString} {inductSort})"
  let fieldArgs := args.extract v.numParams (v.numParams + v.numFields)
  let translatedArgs ← fieldArgs.mapM applyTranslators!
  return some (translatedArgs.foldl appT (symbolT v.name.toString))

end Smt.Translate.Datatype

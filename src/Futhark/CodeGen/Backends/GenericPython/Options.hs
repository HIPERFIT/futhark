-- | This module defines a generator for @getopt@ based command
-- line argument parsing.  Each option is associated with arbitrary
-- Python code that will perform side effects, usually by setting some
-- global variables.
module Futhark.CodeGen.Backends.GenericPython.Options
       ( Option (..)
       , OptionArgument (..)
       , generateOptionParser
       )
       where

import Futhark.CodeGen.Backends.GenericPython.AST

-- | Specification if a single command line option.  The option must
-- have a long name, and may also have a short name.
--
-- When the statement is being executed, the argument (if any) will be
-- stored in the variable @optarg@.
data Option = Option { optionLongName :: String
                     , optionShortName :: Maybe Char
                     , optionArgument :: OptionArgument
                     , optionAction :: [PyStmt]
                     }

-- | Whether an option accepts an argument.
data OptionArgument = NoArgument
                    | RequiredArgument
                    | OptionalArgument

-- | Generate option parsing code that accepts the given command line options.  Will read from @sys.argv@.
--
-- If option parsing fails for any reason, the entire process will
-- terminate with error code 1.
generateOptionParser :: [Option] -> [PyStmt]
generateOptionParser options =
  [Assign (Var "parser")
   (Call "argparse.ArgumentParser"
    [ArgKeyword "description" $
     StringLiteral "A compiled Futhark program."])] ++
  map parseOption options ++
  [Assign (Var "parser_result") $
   Call "vars" [Arg $ Call "parser.parse_args" [Arg $ Var "sys.argv[1:]"]]] ++
  map executeOption options
  where parseOption option =
          Exp $ Call "parser.add_argument" $
          map (Arg . StringLiteral) name_args ++ argument_args
          where name_args = maybe id ((:) . ('-':) . (:[])) (optionShortName option)
                            ["--" ++ optionLongName option]
                argument_args = case optionArgument option of
                  RequiredArgument ->
                    [ArgKeyword "action" (StringLiteral "append"),
                     ArgKeyword "default" $ List []]

                  NoArgument ->
                    [ArgKeyword "action" (StringLiteral "append_const"),
                     ArgKeyword "const" None]

                  OptionalArgument ->
                    [ArgKeyword "action" (StringLiteral "append"),
                     ArgKeyword "default" $ List [],
                     ArgKeyword "nargs" $ StringLiteral "?"]

        executeOption option =
          For "optarg" (Index (Var "parser_result") $
                        IdxExp $ StringLiteral $ fieldName option) $
            optionAction option

        fieldName = map escape . optionLongName
          where escape '-' = '_'
                escape c = c

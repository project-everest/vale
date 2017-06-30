//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
//---------------------------------------------------------------------------------------------
// DafnyDriver
//       - main program for taking a Dafny program and verifying it
//---------------------------------------------------------------------------------------------

namespace DafnyInterface
{
  using System;
  using System.CodeDom.Compiler;
  using System.Collections.Generic;
  using System.Collections.ObjectModel;
  using System.Diagnostics.Contracts;
  using System.IO;
  using System.Reflection;

  using Microsoft.Boogie;
  using Bpl = Microsoft.Boogie;
  using Dafny = Microsoft.Dafny;
  using ExitValue = Microsoft.Dafny.DafnyDriver.ExitValue;

  public class DafnyDriver
  {

    public static int Start_Dafny(string[] args, Dafny.ModuleDecl module, Dafny.BuiltIns builtIns)
    {
      int ret = 0;
      var thread = new System.Threading.Thread(
        new System.Threading.ThreadStart(() =>
          { ret = ThreadMain(args, module, builtIns); }),
          0x10000000); // 256MB stack size to prevent stack overflow
      thread.Start();
      thread.Join();
      return ret;
    }

    public static int ThreadMain(string[] args, Dafny.ModuleDecl module, Dafny.BuiltIns builtIns)
    {
      Contract.Requires(cce.NonNullElements(args));
      Contract.Requires(module != null);
      Contract.Requires(builtIns != null);

      Dafny.ErrorReporter reporter = new Dafny.ConsoleErrorReporter();
      ExecutionEngine.printer = new DafnyConsolePrinter(); // For boogie errors

      Dafny.DafnyOptions.Install(new Dafny.DafnyOptions(reporter));

      // Temporarily change .vad to .dfy
      var valeFileName = args[args.Length - 1];
      args[args.Length - 1] = valeFileName.Replace(".vad", ".dfy");

      List<Microsoft.Dafny.DafnyFile> valeFile;
      List<string> otherFiles;
      ExitValue exitValue = Dafny.DafnyDriver.ProcessCommandLineArguments(args, out valeFile, out otherFiles);

      // Replace .dfy with .vad
      var fileNames = valeFile.ConvertAll(f => f.FilePath);
      fileNames[0] = valeFileName;

      if (exitValue == ExitValue.VERIFIED)
      {
        exitValue = ProcessFile(fileNames, module, builtIns, reporter);
      }

      if (CommandLineOptions.Clo.XmlSink != null) {
        CommandLineOptions.Clo.XmlSink.Close();
      }
      if (CommandLineOptions.Clo.Wait)
      {
        Console.WriteLine("Press Enter to exit.");
        Console.ReadLine();
      }
      if (!Dafny.DafnyOptions.O.CountVerificationErrors && exitValue != ExitValue.PREPROCESSING_ERROR)
      {
         return 0;  
      }
      return (int)exitValue;
    }

    static ExitValue ProcessFile(IList<string> valeFileName, Dafny.ModuleDecl module, Dafny.BuiltIns builtIns,
                                 Dafny.ErrorReporter reporter, string programId = null)
    {
      Contract.Requires(valeFileName.Count == 1);
      Contract.Requires(cce.NonNullElements(valeFileName));

      ExitValue exitValue = ExitValue.VERIFIED;

      Dafny.Program dafnyProgram;
      string programName = valeFileName[0];

      string err = Parse(valeFileName, programName, module, builtIns,  reporter, out dafnyProgram);

      if (err == null) {
        err = Dafny.Main.Resolve(dafnyProgram, reporter);
      }

      if (err != null) {
        exitValue = ExitValue.DAFNY_ERROR;
        ExecutionEngine.printer.ErrorWriteLine(Console.Out, err);
      } else if (dafnyProgram != null && !CommandLineOptions.Clo.NoResolve && !CommandLineOptions.Clo.NoTypecheck
          && Dafny.DafnyOptions.O.DafnyVerify) {
        var boogiePrograms = Dafny.DafnyDriver.Translate(dafnyProgram);

        Dictionary<string, PipelineStatistics> statss;
        PipelineOutcome oc;
        string baseName = cce.NonNull(Path.GetFileName(valeFileName[valeFileName.Count - 1]));
        var verified = Dafny.DafnyDriver.Boogie(baseName, boogiePrograms, programId, out statss, out oc);
        var compiled = Dafny.DafnyDriver.Compile(valeFileName[0], new List<string>().AsReadOnly(), dafnyProgram, oc, statss, verified);

        exitValue = verified && compiled ? ExitValue.VERIFIED : !verified ? ExitValue.NOT_VERIFIED : ExitValue.COMPILE_ERROR;
      }

      if (err == null && dafnyProgram != null && Dafny.DafnyOptions.O.PrintStats) {
        Dafny.Util.PrintStats(dafnyProgram);
      }
      if (err == null && dafnyProgram != null && Dafny.DafnyOptions.O.PrintFunctionCallGraph) {
        Dafny.Util.PrintFunctionCallGraph(dafnyProgram);
      }
      return exitValue;
    }

    public static string Parse(IList<string> fileName, string programName, Dafny.ModuleDecl module, Dafny.BuiltIns builtIns,
                               Dafny.ErrorReporter reporter, out Dafny.Program program)
    {
      Contract.Requires(fileName != null);
      Contract.Requires(programName != null);
      Contract.Requires(fileName.Count == 1);
      program = null;

      if (Bpl.CommandLineOptions.Clo.Trace)
      {
        Console.WriteLine("Finished parsing " + fileName);
      }

      if (!Dafny.DafnyOptions.O.DisallowIncludes)
      {
        string errString = Dafny.Main.ParseIncludes(module, builtIns, fileName, new Dafny.Errors(reporter));
        if (errString != null)
        {
          return errString;
        }
      }

      program = new Dafny.Program(programName, module, builtIns, reporter);

      Dafny.Main.MaybePrintProgram(program, Dafny.DafnyOptions.O.DafnyPrintFile, false);

      return null;
    }

    #region Output

    class DafnyConsolePrinter : ConsolePrinter
    {
      public override void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null)
      {
        base.ReportBplError(tok, message, error, tw, category);

        if (tok is Dafny.NestedToken)
        {
          var nt = (Dafny.NestedToken)tok;
          ReportBplError(nt.Inner, "Related location", false, tw);
        }
      }
    }

    #endregion

    #region Parsing Vale

    public static int Parse_Verbatim_Block(string verbatim_block, string filename, int line, Dafny.ModuleDecl module,
                                           Dafny.BuiltIns builtIns, bool verifyThisFile = true)
    {
      Contract.Requires(verbatim_block != null);
      Contract.Requires(filename != null);
      Contract.Requires(module != null);

      Dafny.ErrorReporter reporter = new Dafny.ConsoleErrorReporter();
      Dafny.Errors errors = new Dafny.Errors(reporter);

      byte[] buffer = cce.NonNull(System.Text.UTF8Encoding.Default.GetBytes(verbatim_block));
      MemoryStream ms = new MemoryStream(buffer, false);
      string fullFilename = Path.GetFullPath(filename);
      Dafny.Scanner scanner = new Dafny.Scanner(ms, errors, fullFilename, filename, line);
      Dafny.Parser parser = new Dafny.Parser(scanner, errors, null, module, builtIns, verifyThisFile);
      parser.Parse();
      return parser.errors.ErrorCount;
    }

    #endregion

  }
}

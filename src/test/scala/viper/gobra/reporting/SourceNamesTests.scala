// This Source Code Form is subject to the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.gobra.reporting

import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Paths}

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import viper.gobra.Gobra
import viper.gobra.ast.{frontend => p, internal => in}
import viper.gobra.frontend.{Config, Source => GobraSource}
import viper.gobra.reporting.Source.RichViperNode
import viper.gobra.theory.Addressability
import viper.gobra.util.{DefaultGobraExecutionContext, TypeBounds}
import viper.silver.{ast => vpr}

import scala.concurrent.{Await, Promise}
import scala.concurrent.duration._

class SourceNamesTests extends AnyFunSuite with Matchers {
  private val intType = in.IntT(Addressability.Exclusive, TypeBounds.DefaultInt)
  private val receiverType = p.PMethodReceiveName(p.PNamedOperand(p.PIdnUse("Counter")))

  private def metadata(node: p.PNode): Source.Parser.Info =
    Source.Parser.Single(node, Source.Origin(vpr.SourcePosition(Paths.get("names.gobra"), 1, 1), "source"))

  private def declaration(variable: in.Var): vpr.LocalVarDecl =
    vpr.LocalVarDecl(variable.id, vpr.Int)().withInfo(variable)

  private def read(variable: in.Var): vpr.LocalVar =
    vpr.LocalVar(variable.id, vpr.Int)().withInfo(variable)

  private def functionSource(name: String, pure: Boolean = false): p.PFunctionDecl =
    p.PFunctionDecl(p.PIdnDef(name), Vector.empty, p.PResult(Vector.empty),
      p.PFunctionSpec(Vector.empty, Vector.empty, Vector.empty, isPure = pure), None)

  private def invocation(name: String): Source.Parser.Info =
    metadata(p.PInvoke(p.PNamedOperand(p.PIdnUse(name)), Vector.empty, None))

  private def functionApp(name: String, source: in.Node): vpr.FuncApp =
    vpr.FuncApp(name, Seq.empty)(vpr.NoPosition, vpr.NoInfo, vpr.Int, vpr.NoTrafos).withInfo(source)

  private val receiver = in.Parameter.In("receiver_V0", intType)(
    metadata(p.PNamedReceiver(p.PIdnDef("receiver"), receiverType, addressable = false)))
  private val result = in.Parameter.Out("result_V0", intType)(
    metadata(p.PNamedParameter(p.PIdnDef("result"), p.PIntType())))

  test("local declarations and reads retain source spelling across generated copies") {
    val name = "input_V0_CN3_with_underscores"
    Seq[p.PIdnNode](p.PIdnDef(name), p.PIdnUse(name), p.PIdnUnk(name)).foreach { id =>
      Seq(s"${name}_V2", s"${name}_V2_CN3").foreach { encoded =>
        val variable = in.LocalVar(encoded, intType)(metadata(id))
        SourceNames.fromViper(declaration(variable)) should be (Some(name))
        SourceNames.fromViper(read(variable)) should be (Some(name))
      }
    }
  }

  test("named input and output parameters recover their declared names") {
    val input = in.Parameter.In("input_V0", intType)(metadata(p.PNamedParameter(p.PIdnDef("input"), p.PIntType())))
    val output = in.Parameter.Out("result_V0", intType)(metadata(p.PNamedParameter(p.PIdnDef("result"), p.PIntType())))
    SourceNames.fromViper(declaration(input)) should be (Some("input"))
    SourceNames.fromViper(read(output)) should be (Some("result"))
  }

  test("named receiver parameters recover their declared names") {
    val source = p.PNamedReceiver(p.PIdnDef("counter_ref"), receiverType, addressable = true)
    val receiver = in.Parameter.In("counter_ref_V0", intType)(metadata(source))
    SourceNames.fromViper(declaration(receiver)) should be (Some("counter_ref"))
  }

  test("explicitly ghost parameters recover their names") {
    val source = p.PExplicitGhostParameter(p.PNamedParameter(p.PIdnDef("ghost_count"), p.PIntType()))
    val parameter = in.Parameter.In("ghost_count_V0", intType)(metadata(source))
    SourceNames.fromViper(declaration(parameter)) should be (Some("ghost_count"))
  }

  test("quantified variables recover names from bound variable metadata") {
    val source = p.PBoundVariable(p.PIdnDef("bound_index"), p.PIntType())
    val variable = in.BoundVar("bound_index_V0", intType)(metadata(source))
    SourceNames.fromViper(declaration(variable)) should be (Some("bound_index"))
  }

  test("unnamed parameters, receivers, and blank identifiers have no source name") {
    val sources = Seq[p.PNode](
      p.PUnnamedParameter(p.PIntType()),
      p.PExplicitGhostParameter(p.PUnnamedParameter(p.PIntType())),
      p.PUnnamedReceiver(receiverType),
      p.PNamedParameter(p.PIdnDef("_"), p.PIntType()),
      p.PWildcard()
    )
    sources.foreach { source =>
      val parameter = in.Parameter.In("generated_PI0", intType)(metadata(source))
      SourceNames.fromViper(declaration(parameter)) should be (None)
    }
  }

  test("field access metadata removes only the appended A from a field name") {
    Seq("value", "valueA", "field_with_underscores").foreach { name =>
      val field = in.Field(s"${name}A", intType, ghost = false)(Source.Parser.Internal)
      val receiver = in.LocalVar("receiver_V0", in.StructT(Vector(field), ghost = false, addressability = Addressability.Exclusive))(Source.Parser.Internal)
      val source = p.PDot(p.PNamedOperand(p.PIdnUse("receiver")), p.PIdnUse(name))
      val reference = in.FieldRef(receiver, field)(metadata(source))
      val getter = vpr.DomainFuncApp("ShStructget0of1", Seq(vpr.LocalVar("receiver_V0", vpr.Ref)()), Map.empty)(
        vpr.NoPosition, vpr.NoInfo, vpr.Ref, "ShStruct1", vpr.NoTrafos
      ).withInfo(reference)
      SourceNames.fromViper(getter) should be (Some(name))
    }
  }

  test("unknown metadata and non-variable expressions do not acquire variable names") {
    SourceNames.fromViper(vpr.LocalVar("generated_V0", vpr.Int)()) should be (None)
    val synthesized = in.LocalVar("generated_V0", intType)(metadata(p.PIntType()))
    SourceNames.fromViper(declaration(synthesized)) should be (None)
    // A declaration without an identifier cannot supply a source variable name.
    val unknown = in.LocalVar("generated_V0", intType)(metadata(p.PUnnamedParameter(p.PIntType())))
    SourceNames.fromViper(declaration(unknown)) should be (None)
    val literal = in.IntLit(1)(metadata(p.PIdnUse("not_a_variable")))
    SourceNames.fromViper(vpr.IntLit(1)().withInfo(literal)) should be (None)
  }

  test("function and pure function declarations recover source names from their proxies") {
    val name = "compute_FP0_CN3_with_underscores"
    val source = functionSource(name)
    val proxy = in.FunctionProxy(s"${name}_package_F0")(metadata(source))
    val function = in.Function(proxy, Vector.empty, Vector.empty, Vector.empty, Vector.empty,
      Vector.empty, Vector.empty, None)(metadata(source))
    val pureFunction = in.PureFunction(proxy, Vector.empty, Vector(result), Vector.empty, Vector.empty,
      Vector.empty, Vector.empty, None, isOpaque = true)(metadata(source))
    SourceNames.fromViper(vpr.Method(proxy.name, Seq.empty, Seq.empty, Seq.empty, Seq.empty, None)()
      .withInfo(function)) should be (Some(name))
    SourceNames.fromViper(vpr.Function(proxy.name, Seq.empty, vpr.Int, Seq.empty, Seq.empty, None)()
      .withInfo(pureFunction)) should be (Some(name))
  }

  test("method and pure method declarations retain names including interface signatures") {
    val name = "Value_M0_CN3"
    val spec = p.PFunctionSpec(Vector.empty, Vector.empty, Vector.empty)
    val sources = Seq[p.PNode](
      p.PMethodDecl(p.PIdnDef(name), p.PUnnamedReceiver(receiverType), Vector.empty,
        p.PResult(Vector.empty), spec, None),
      p.PMethodSig(p.PIdnDef(name), Vector.empty, p.PResult(Vector.empty), spec, isGhost = false)
    )
    sources.foreach { source =>
      val proxy = in.MethodProxy(name, s"${name}_Counter_package_M0")(metadata(source))
      val method = in.Method(receiver, proxy, Vector.empty, Vector.empty, Vector.empty, Vector.empty,
        Vector.empty, Vector.empty, None)(metadata(source))
      val pureMethod = in.PureMethod(receiver, proxy, Vector.empty, Vector(result), Vector.empty, Vector.empty,
        Vector.empty, Vector.empty, None, isOpaque = false)(metadata(source))
      SourceNames.fromViper(vpr.Method(proxy.uniqueName, Seq.empty, Seq.empty, Seq.empty, Seq.empty, None)()
        .withInfo(method)) should be (Some(name))
      SourceNames.fromViper(vpr.Function(proxy.uniqueName, Seq.empty, vpr.Int, Seq.empty, Seq.empty, None)()
        .withInfo(pureMethod)) should be (Some(name))
    }
  }

  test("predicate declarations recover function and method names including interface signatures") {
    val name = "Valid_P0_CN3"
    val source = p.PFPredicateDecl(p.PIdnDef(name), Vector.empty, None)
    val proxy = in.FPredicateProxy(s"${name}_package_P0")(metadata(source))
    val predicate = in.FPredicate(proxy, Vector.empty, None)(metadata(source))
    SourceNames.fromViper(vpr.Predicate(proxy.name, Seq.empty, None)().withInfo(predicate)) should be (Some(name))

    val methodSources = Seq[p.PNode](
      p.PMPredicateDecl(p.PIdnDef(name), p.PUnnamedReceiver(receiverType), Vector.empty, None),
      p.PMPredicateSig(p.PIdnDef(name), Vector.empty)
    )
    methodSources.foreach { methodSource =>
      val methodProxy = in.MPredicateProxy(name, s"${name}_Counter_package_P0")(metadata(methodSource))
      val methodPredicate = in.MPredicate(receiver, methodProxy, Vector.empty, None)(metadata(methodSource))
      SourceNames.fromViper(vpr.Predicate(methodProxy.uniqueName, Seq.empty, None)()
        .withInfo(methodPredicate)) should be (Some(name))
    }
  }

  test("function and pure function calls use proxy identifiers instead of invocation metadata") {
    val name = "compute_F0_CN3"
    Seq[p.PIdnNode](p.PIdnUse(name), p.PIdnDef(name), p.PIdnUnk(name)).foreach { id =>
      val proxy = in.FunctionProxy(s"${name}_package_F0")(metadata(id))
      val call = in.FunctionCall(Vector.empty, proxy, Vector.empty)(invocation(name))
      val pureCall = in.PureFunctionCall(proxy, Vector.empty, intType)(invocation(name))
      SourceNames.fromViper(vpr.MethodCall(proxy.name, Seq.empty, Seq.empty)(vpr.NoPosition, vpr.NoInfo, vpr.NoTrafos)
        .withInfo(call)) should be (Some(name))
      SourceNames.fromViper(functionApp(proxy.name, pureCall)) should be (Some(name))
    }
  }

  test("method and pure method calls recover the retained name without proxy source metadata") {
    val name = "Value_M0_CN3"
    val proxy = in.MethodProxy(name, s"${name}_Counter_package_M0")(Source.Parser.Internal)
    val call = in.MethodCall(Vector.empty, receiver, proxy, Vector.empty)(invocation(name))
    val pureCall = in.PureMethodCall(receiver, proxy, Vector.empty, intType)(invocation(name))
    SourceNames.fromViper(vpr.MethodCall(proxy.uniqueName, Seq.empty, Seq.empty)(vpr.NoPosition, vpr.NoInfo, vpr.NoTrafos)
      .withInfo(call)) should be (Some(name))
    SourceNames.fromViper(functionApp(proxy.uniqueName, pureCall)) should be (Some(name))
  }

  test("predicate accesses unwrap permission assertions and retain dynamic-family access names") {
    val name = "Valid_P0_CN3"
    val functionProxy = in.FPredicateProxy(s"${name}_package_P0")(metadata(p.PIdnUse(name)))
    val methodProxy = in.MPredicateProxy(name, s"${name}_Counter_package_P0")(Source.Parser.Internal)
    val accesses = Seq(
      functionProxy.name -> in.FPredicateAccess(functionProxy, Vector.empty)(invocation(name)),
      methodProxy.uniqueName -> in.MPredicateAccess(receiver, methodProxy, Vector.empty)(invocation(name))
    )
    accesses.foreach { case (encoded, access) =>
      val accessible = in.Accessible.Predicate(access)
      val assertion = in.Access(accessible, in.FullPerm(Source.Parser.Internal))(invocation(name))
      Seq[in.Node](access, accessible, assertion).foreach { source =>
        Seq(encoded, "dynamic_pred_12").foreach { predicateName =>
          val viperAccess = vpr.PredicateAccess(Seq.empty, predicateName)().withInfo(source)
          SourceNames.fromViper(viperAccess) should be (Some(name))
          SourceNames.fromViper(vpr.PredicateAccessPredicate(viperAccess, Some(vpr.FullPerm()()))()
            .withInfo(source)) should be (Some(name))
        }
      }
    }
    SourceNames.fromViper(vpr.Predicate("dynamic_pred_12", Seq.empty, None)()) should be (None)
  }

  test("member names survive compound metadata used by opaque functions and revealed calls") {
    val name = "opaque_function"
    val proxy = in.FunctionProxy(s"${name}_package_F0")(metadata(functionSource(name, pure = true)))
    val function = in.PureFunction(proxy, Vector.empty, Vector(result), Vector.empty, Vector.empty,
      Vector.empty, Vector.empty, None, isOpaque = true)(metadata(functionSource(name, pure = true)))
    val declaration = vpr.Function(proxy.name, Seq.empty, vpr.Int, Seq.empty, Seq.empty, None)().withInfo(function)
    val call = functionApp(proxy.name, in.PureFunctionCall(proxy, Vector.empty, intType, reveal = true)(invocation(name)))
    Seq[vpr.Node](declaration, call).foreach { node =>
      val (pos, info, errT) = node.getPrettyMetadata
      val annotated = node.withMeta(pos, vpr.ConsInfo(vpr.SimpleInfo(Seq("annotation")), info), errT)
      SourceNames.fromViper(annotated) should be (Some(name))
    }
  }

  test("generated helpers and missing source names do not acquire unrelated member names") {
    val name = "compute"
    val proxy = in.FunctionProxy("compute_package_F0")(metadata(functionSource(name)))
    val call = in.PureFunctionCall(proxy, Vector.empty, intType)(invocation(name))
    SourceNames.fromViper(vpr.IntLit(1)().withInfo(call)) should be (None)
    SourceNames.fromViper(functionApp("generated_helper", call)) should be (None)
    val function = in.PureFunction(proxy, Vector.empty, Vector(result), Vector.empty, Vector.empty,
      Vector.empty, Vector.empty, None, isOpaque = false)(metadata(functionSource(name)))
    SourceNames.fromViper(vpr.Function("generated_helper", Seq.empty, vpr.Int, Seq.empty, Seq.empty, None)()
      .withInfo(function)) should be (None)

    Seq(Source.Parser.Internal, metadata(p.PIntType()), metadata(p.PIdnUse("_"))).foreach { info =>
      val unknown = in.FunctionProxy("generated_F0")(info)
      val unknownCall = in.PureFunctionCall(unknown, Vector.empty, intType)(invocation(name))
      SourceNames.fromViper(functionApp(unknown.name, unknownCall)) should be (None)
    }
    val predicate = in.FPredicateProxy("generated_P0")(Source.Parser.Internal)
    val access = in.FPredicateAccess(predicate, Vector.empty)(invocation("unrelated"))
    SourceNames.fromViper(vpr.PredicateAccess(Seq.empty, predicate.name)().withInfo(access)) should be (None)
  }

  test("source member names survive parsing, desugaring, and Viper encoding") {
    val program = """package names
      |type Counter struct {}
      |pred Valid_F0() { true }
      |pred (c Counter) Valid_M0() { true }
      |func Write_F0() {}
      |func (c Counter) Write_M0() {}
      |pure func Read_F0() int { return 0 }
      |pure func (c Counter) Read_M0() int { return 0 }
      |func Use(c Counter) {
      |  Write_F0()
      |  c.Write_M0()
      |  assert Read_F0() == c.Read_M0()
      |  fold Valid_F0()
      |  unfold Valid_F0()
      |  fold c.Valid_M0()
      |  unfold c.Valid_M0()
      |}
      |""".stripMargin
    val directory = Files.createTempDirectory("gobra-source-names")
    val file = directory.resolve("names.gobra")
    val executor = new DefaultGobraExecutionContext()
    try {
      Files.write(file, program.getBytes(UTF_8))
      val source = GobraSource.FromFileSource(file)
      val pkg = GobraSource.getPackageInfoOrCrash(source, Paths.get(""))
      val translated = Promise[vpr.Program]()
      val reporter = new GobraReporter {
        override val name: String = "source-name-test"
        override def report(message: GobraMessage): Unit = message match {
          case generated: GeneratedViperMessage => translated.trySuccess(generated.vprAst()); ()
          case _ =>
        }
      }
      val config = Config(
        reporter = reporter,
        packageInfoInputMap = Map(pkg -> Vector(source)),
        shouldVerify = false,
        disableCheckTerminationPureFns = true)
      Await.result(new Gobra().verify(pkg, config)(executor), 60.seconds) should be (VerifierResult.Skipped)
      val encoded = Await.result(translated.future, 5.seconds)
      encoded.methods.flatMap(SourceNames.fromViper).toSet should contain allOf ("Write_F0", "Write_M0", "Use")
      encoded.functions.flatMap(SourceNames.fromViper).toSet should contain allOf ("Read_F0", "Read_M0")
      encoded.predicates.flatMap(SourceNames.fromViper).toSet should contain allOf ("Valid_F0", "Valid_M0")

      val calls = scala.collection.mutable.Set.empty[String]
      encoded.visit {
        case node: vpr.MethodCall => calls ++= SourceNames.fromViper(node)
        case node: vpr.FuncApp => calls ++= SourceNames.fromViper(node)
        case node: vpr.PredicateAccess => calls ++= SourceNames.fromViper(node)
      }
      calls.toSet should contain allOf ("Write_F0", "Write_M0", "Read_F0", "Read_M0", "Valid_F0", "Valid_M0")
    } finally {
      executor.terminateAndAssertInexistanceOfTimeout()
      Files.deleteIfExists(file)
      Files.deleteIfExists(directory)
    }
  }
}

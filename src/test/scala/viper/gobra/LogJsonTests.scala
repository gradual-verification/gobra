// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.gobra

import java.nio.file.{Files, Path}
import org.scalatest.funsuite.AnyFunSuite
import spray.json._
import viper.gobra.frontend.{Config, InputConfig, ScallopGobraConfig}
import viper.gobra.reporting.{NoopReporter, VerifierResult}
import viper.gobra.util.DefaultGobraExecutionContext

import scala.concurrent.Await
import scala.concurrent.duration._
import scala.jdk.CollectionConverters._

class LogJsonTests extends AnyFunSuite {
  private def withDirectory(test: Path => Unit): Unit = {
    val directory = Files.createTempDirectory("gobra-log-json-tests")
    try test(directory)
    finally {
      val files = Files.list(directory)
      try files.iterator().asScala.foreach(Files.delete(_))
      finally files.close()
      Files.delete(directory)
    }
  }

  private def config(args: String*): Config =
    new ScallopGobraConfig(args, isInputOptional = true).config.fold(
      errors => fail(errors.map(_.formattedMessage).mkString("\n")), identity)

  private def verify(config: Config): VerifierResult = {
    val executor = new DefaultGobraExecutionContext()
    try Await.result(new Gobra().verify(config.packageInfoInputMap.keys.head,
      config.copy(reporter = NoopReporter))(executor), 60.seconds)
    finally executor.terminateAndAssertInexistanceOfTimeout()
  }

  private def entries(file: Path): Vector[JsObject] = {
    val methods = Files.readString(file).parseJson.asJsObject.fields.values.toVector
    assert(methods.nonEmpty)
    methods.flatMap {
      case JsArray(records) => records.map(_.asJsObject)
      case other => fail(s"Expected a method log array, got $other")
    }
  }

  test("logJson defaults to false and survives CLI and in-file configuration merging") {
    assert(!config().logJson)
    val enabled = new ScallopGobraConfig(Seq("--logJson"), isInputOptional = true).toInputConfig
    assert(enabled.config(isInputOptional = true).exists(_.logJson))
    assert(Config().applyInputConfig(enabled).logJson)
    assert((InputConfig() orElse enabled).config(isInputOptional = true).exists(_.logJson))
    assert((InputConfig() merge enabled).config(isInputOptional = true).exists(_.logJson))
  }

  test("logJson exports every method to its input's JSON file and preserves chopped reports") {
    withDirectory { directory =>
      val first = directory.resolve("first.test.gobra")
      val second = directory.resolve("second.go")
      Files.writeString(first,
        "package main\nfunc first() { assert true }\nfunc another() { assert true }\n")
      Files.writeString(second, "package main\nfunc second() {\n  //@ assert true\n}\n")
      val cfg = config("-i", first.toString, second.toString, "--logJson", "--chop", "2")
      assert(verify(cfg) == VerifierResult.Success)
      val firstOutput = directory.resolve("first.test.json")
      val secondOutput = directory.resolve("second.json")
      // Gobra also generates initialization methods, which are exported alongside source methods.
      val firstMethods = Files.readString(firstOutput).parseJson.asJsObject.fields.keySet
      val secondMethods = Files.readString(secondOutput).parseJson.asJsObject.fields.keySet
      assert(firstMethods.exists(_.startsWith("first_")))
      assert(firstMethods.exists(_.startsWith("another_")))
      assert(!firstMethods.exists(_.startsWith("second_")))
      assert(secondMethods.exists(_.startsWith("second_")))
      assert(!secondMethods.exists(_.startsWith("first_")))
      assert(entries(firstOutput).exists(_.fields.get("line").contains(JsNumber(3))))
      assert(entries(secondOutput).exists(_.fields.get("line").contains(JsNumber(3))))
      assert(!Files.exists(directory.resolve("first.test.gobra.json")))
    }
  }

  test("logJson exports traces when verification fails") {
    withDirectory { directory =>
      val input = directory.resolve("failure.gobra")
      Files.writeString(input, "package main\nfunc failure() { assert false }\n")
      assert(verify(config("-i", input.toString, "--logJson")).isInstanceOf[VerifierResult.Failure])
      val records = entries(directory.resolve("failure.json"))
      assert(records.exists(_.fields.get("line").contains(JsNumber(2))))
      assert(records.exists(_.fields.get("kind").contains(JsString("error"))))
    }
  }

  test("verification without logJson does not create a JSON file") {
    withDirectory { directory =>
      val input = directory.resolve("disabled.gobra")
      Files.writeString(input, "package main\nfunc disabled() { assert true }\n")
      assert(verify(config("-i", input.toString)) == VerifierResult.Success)
      assert(!Files.exists(directory.resolve("disabled.json")))
    }
  }
}

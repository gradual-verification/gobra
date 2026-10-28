// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.gobra.reporting

import java.nio.file.{Files, Path}
import spray.json.{JsArray, JsObject}
import viper.silicon.logger.MemberSymbExLogger
import viper.silver.ast.{AbstractSourcePosition, Method}
import viper.silver.reporter.ExecutionTraceReport

/** Writes method logs beside their source files, accumulating reports from chopped verification tasks. */
class JsonSymbExLogWriter(inputs: Vector[Path]) {
  private var logs: Map[Path, Map[String, JsArray]] =
    inputs.map(path => path.toAbsolutePath.normalize() -> Map.empty[String, JsArray]).toMap

  def write(trace: ExecutionTraceReport): Unit = synchronized {
    trace.memberTraces.foreach {
      case log: MemberSymbExLogger if log.member.isInstanceOf[Method] =>
        log.member.pos match {
          case pos: AbstractSourcePosition =>
            val input = pos.file.toAbsolutePath.normalize()
            logs.get(input).foreach { methods =>
              logs += input -> (methods + (log.member.name -> log.logToJson))
            }
          case _ =>
        }
      case _ =>
    }
    logs.foreach { case (input, methods) =>
      val name = input.getFileName.toString
      val extension = name.lastIndexOf('.')
      val baseName = if (extension > 0) name.substring(0, extension) else name
      val output = input.resolveSibling(s"$baseName.json")
      Files.writeString(output, JsObject(methods).prettyPrint)
    }
  }
}

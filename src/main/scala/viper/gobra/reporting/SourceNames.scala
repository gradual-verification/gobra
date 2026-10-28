// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.gobra.reporting

import viper.gobra.ast.{frontend, internal}
import viper.silver.{ast => vpr}

/** Recovers display names without changing the identifiers used for verification. */
object SourceNames {
  def fromViper(node: vpr.Node): Option[String] = Source.unapply(node).flatMap { info =>
    info.node match {
      // Desugar's NameManager.field appends exactly one "A" to the source field name.
      case internal.FieldRef(_, field) => Some(field.name.stripSuffix("A"))
      case _: internal.LocalVar | _: internal.BoundVar | _: internal.Parameter =>
        identifier(info.pnode)
      case _ => memberProxy(node, info.node).flatMap(memberName)
    }
  }

  private def memberProxy(node: vpr.Node, source: internal.Node): Option[internal.Proxy] = {
    // Encodings can attach the same source metadata to auxiliary expressions and
    // declarations. Only the corresponding member or invocation has its name.
    val proxy: Option[internal.Proxy] = (node, source) match {
      case (_: vpr.Method, member: internal.Function) => Some(member.name)
      case (_: vpr.Method, member: internal.Method) => Some(member.name)
      case (_: vpr.Function, member: internal.PureFunction) => Some(member.name)
      case (_: vpr.Function, member: internal.PureMethod) => Some(member.name)
      case (_: vpr.Predicate, member: internal.FPredicate) => Some(member.name)
      case (_: vpr.Predicate, member: internal.MPredicate) => Some(member.name)
      case (_: vpr.MethodCall, call: internal.FunctionCall) => Some(call.func)
      case (_: vpr.MethodCall, call: internal.MethodCall) => Some(call.meth)
      case (_: vpr.FuncApp, call: internal.PureFunctionCall) => Some(call.func)
      case (_: vpr.FuncApp, call: internal.PureMethodCall) => Some(call.meth)
      // Dynamic predicate families have generated names, but an individual
      // access still identifies the source predicate that was invoked.
      case (_: vpr.PredicateAccess | _: vpr.PredicateAccessPredicate, _) =>
        return predicateProxy(source)
      case _ => None
    }
    proxy.filter { p =>
      val encoded = p match {
        case member: internal.MemberProxy => member.uniqueName
        case _ => p.name
      }
      node match {
        case member: vpr.Member => member.name == encoded
        case call: vpr.MethodCall => call.methodName == encoded
        case call: vpr.FuncApp => call.funcname == encoded
        case _ => false
      }
    }
  }

  private def predicateProxy(node: internal.Node): Option[internal.PredicateProxy] = node match {
    case internal.Access(internal.Accessible.Predicate(access), _) => predicateProxy(access)
    case internal.Accessible.Predicate(access) => predicateProxy(access)
    case internal.FPredicateAccess(pred, _) => Some(pred)
    case internal.MPredicateAccess(_, pred, _) => Some(pred)
    case _ => None
  }

  private def memberName(proxy: internal.Proxy): Option[String] = proxy match {
    case method: internal.MethodProxy => Some(method.name).filterNot(_ == "_")
    case predicate: internal.MPredicateProxy => Some(predicate.name).filterNot(_ == "_")
    case _: internal.FunctionProxy | _: internal.FPredicateProxy => proxy.info match {
      case Source.Parser.Single(node, _) => node match {
        case declaration: frontend.PFunctionDecl => identifier(declaration.id)
        case declaration: frontend.PFPredicateDecl => identifier(declaration.id)
        case _ => identifier(node)
      }
      case _ => None
    }
    case _ => None
  }

  private def identifier(node: frontend.PNode): Option[String] = {
    val name = node match {
      case frontend.PIdnDef(name) => Some(name)
      case frontend.PIdnUse(name) => Some(name)
      case frontend.PIdnUnk(name) => Some(name)
      case frontend.PNamedParameter(id, _) => Some(id.name)
      case frontend.PNamedReceiver(id, _, _) => Some(id.name)
      case frontend.PBoundVariable(id, _) => Some(id.name)
      case frontend.PExplicitGhostParameter(actual) => identifier(actual)
      case _ => None
    }
    name.filterNot(_ == "_")
  }
}

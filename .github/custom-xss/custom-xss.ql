/**
 * @name Cross-site scripting
 * @description Writing user input directly to a web page
 *              allows for a cross-site scripting vulnerability.
 * @kind path-problem
 * @problem.severity error
 * @security-severity 6.1
 * @precision high
 * @id java/xss
 * @tags security
 *       external/cwe/cwe-079
 */

import java
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.security.XSS
import DataFlow::PathGraph
private import semmle.code.java.dataflow.ExternalFlow

private class WebGoatSummaries extends SummaryModelCsv {
  override predicate row(string row) {
    row =
      [
        //`namespace; type; subtypes; name; signature; ext; input; output; kind`
        "org.owasp.webgoat.assignments;AttackResult;false;AttackResult;;;Argument[1];Argument[-1];taint",
        "org.owasp.webgoat.assignments;AttackResult;false;AttackResult;;;Argument[2];Argument[-1];taint",
        "org.owasp.webgoat.assignments;AttackResult;false;AttackResult;;;Argument[3];Argument[-1];taint",
        "org.springframework.context.support;AbstractMessageSource;true;getMessage;(String,Object[],String,Locale);;ArrayElement of Argument[1];ReturnValue;taint",
        "org.springframework.context.support;AbstractMessageSource;true;getMessage;(String,Object[],String,Locale);;Argument[2];ReturnValue;taint",
        "org.springframework.context.support;AbstractMessageSource;true;getMessage;(String,Object[],Locale);;ArrayElement of Argument[1];ReturnValue;taint",
        "org.springframework.context.support;AbstractMessageSource;true;getMessageFromParent;;;ArrayElement of Argument[1];ReturnValue;taint",
      ]
  }
}

class WebGoatSink extends XssSink {
  WebGoatSink() {
    exists(SpringRequestMappingMethod requestMappingMethod, ReturnStmt rs |
      requestMappingMethod = rs.getEnclosingCallable() and
      this.asExpr() = rs.getResult()
    |
      requestMappingMethod
          .getReturnType()
          .(RefType)
          .hasQualifiedName("org.owasp.webgoat.assignments", "AttackResult")
    )
  }
}

class XSSConfig extends TaintTracking::Configuration {
  XSSConfig() { this = "XSSConfig" }

  override predicate isSource(DataFlow::Node source) { source instanceof RemoteFlowSource }

  override predicate isSink(DataFlow::Node sink) { sink instanceof XssSink }

  override predicate isSanitizer(DataFlow::Node node) { node instanceof XssSanitizer }

  override predicate isSanitizerOut(DataFlow::Node node) { node instanceof XssSinkBarrier }

  override predicate isAdditionalTaintStep(DataFlow::Node node1, DataFlow::Node node2) {
    any(XssAdditionalTaintStep s).step(node1, node2)
  }
}

from DataFlow::PathNode source, DataFlow::PathNode sink, XSSConfig conf
where conf.hasFlowPath(source, sink)
select sink.getNode(), source, sink, "Cross-site scripting vulnerability due to $@.",
  source.getNode(), "user-provided value"

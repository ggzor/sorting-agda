import React from "react";
import { Prism as Code } from "react-syntax-highlighter";

const style = {
  'pre[class*="language-"]': {
    backgroundColor: "#011627",
    color: "#d6deeb",
    padding: "1em",
    borderRadius: "5px",
  },
  'code[class*="language-"]': {
    backgroundColor: "#011627",
    color: "#d6deeb",
    fontFamily:
      '"Consolas", "Bitstream Vera Sans Mono", "Courier New", Courier, monospace',
    direction: "ltr",
    textAlign: "left",
    whiteSpace: "pre",
    wordSpacing: "normal",
    wordBreak: "normal",
    fontSize: ".9em",
    lineHeight: "1.2em",
    MozTabSize: "4",
    OTabSize: "4",
    tabSize: "4",
    WebkitHyphens: "none",
    MozHyphens: "none",
    msHyphens: "none",
    hyphens: "none",
  },
  punctuation: {
    color: "#7fdbca",
  },
  operator: {
    color: "#7fdbca",
  },
};

const getLanguage = (className) => {
  const match = /language-(\w*)/.exec(className || "language-javascript");
  let lang = "javascript";
  if (match && match.length > 1) {
    lang = match[1];
  }
  return lang;
};

export const code = ({ children, className, ...props }) => {
  return (
    <Code language={getLanguage(className)} style={style}>
      {children.trimEnd("\n")}
    </Code>
  );
};

export const pre = (props) => props.children;

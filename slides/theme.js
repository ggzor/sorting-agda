import { themes } from "mdx-deck";
import { code, pre } from "./components";

export const theme = {
  ...themes.future,
  components: {
    code,
    pre,
  },
};
theme.colors = {
  ...theme.colors,
  backdrop: "#2e2e2e",
};
theme.styles = {
  ...theme.styles,
  h1: {
    textTransform: "none",
    letterSpacing: 0,
    textAlign: "center",
  },
  h3: {
    letterSpacing: 0,
  },
  img: {
    height: "min-content",
    borderRadius: "5px",
  },
  ul: {
    alignSelf: "flex-start",
  },
};

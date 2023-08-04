/*
 * SPDX-FileCopyrightText: 2021-2023 The Refinery Authors <https://refinery.tools/>
 *
 * SPDX-License-Identifier: EPL-2.0
 */
package tools.refinery.visualization.internal;

import tools.refinery.store.map.Version;
import tools.refinery.store.model.Interpretation;
import tools.refinery.store.model.Model;
import tools.refinery.store.representation.AnySymbol;
import tools.refinery.store.representation.TruthValue;
import tools.refinery.store.tuple.Tuple;
import tools.refinery.visualization.ModelVisualizerAdapter;
import tools.refinery.visualization.ModelVisualizerStoreAdapter;

import java.io.*;
import java.util.*;
import java.util.stream.Collectors;

public class ModelVisualizerAdapterImpl implements ModelVisualizerAdapter {
	private final Model model;
	private final ModelVisualizerStoreAdapter storeAdapter;
	private final Map<AnySymbol, Interpretation<?>> interpretations;
	private final StringBuilder designSpaceBuilder = new StringBuilder();
	private final Map<Version, Integer> states = new HashMap<>();
	private int transitionCounter = 0;
	private Integer numberOfStates = 0;
	private static final Map<Object, String> truthValueToDot = new HashMap<>()
	{{
		put(TruthValue.TRUE, "1");
		put(TruthValue.FALSE, "0");
		put(TruthValue.UNKNOWN, "½");
		put(TruthValue.ERROR, "E");
		put(true, "1");
		put(false, "0");
	}};

	public ModelVisualizerAdapterImpl(Model model, ModelVisualizerStoreAdapter storeAdapter) {
		this.model = model;
		this.storeAdapter = storeAdapter;
		this.interpretations = new HashMap<>();
		for (var symbol : storeAdapter.getStore().getSymbols()) {
			var arity = symbol.arity();
			if (arity < 1 || arity > 2) {
				continue;
			}
			var interpretation = (Interpretation<?>) model.getInterpretation(symbol);
			interpretations.put(symbol, interpretation);
		}
		designSpaceBuilder.append("digraph designSpace {\n");
		designSpaceBuilder.append("""
				node[
					style=filled
					fillcolor=white
				]
				""");
	}

	@Override
	public Model getModel() {
		return model;
	}

	@Override
	public ModelVisualizerStoreAdapter getStoreAdapter() {
		return storeAdapter;
	}

	@Override
	public String createDotForCurrentModelState() {

		var unaryTupleToInterpretationsMap = new HashMap<Tuple, LinkedHashSet<Interpretation<?>>>();

		var sb = new StringBuilder();

		sb.append("digraph model {\n");
		sb.append("""
				node [
				\tstyle="filled, rounded"
				\tshape=plain
				\tpencolor="#00000088"
				\tfontname="Helvetica"
				]
				""");
		sb.append("""
				edge [
				\tlabeldistance=3
				\tfontname="Helvetica"
				]
				""");

		for (var entry : interpretations.entrySet()) {
			var key = entry.getKey();
			var arity = key.arity();
			var cursor = entry.getValue().getAll();
			if (arity == 1) {
				while (cursor.move()) {
					unaryTupleToInterpretationsMap.computeIfAbsent(cursor.getKey(), k -> new LinkedHashSet<>())
							.add(entry.getValue());
				}
			} else if (arity == 2) {
				while (cursor.move()) {
					var tuple = cursor.getKey();
					for (var i = 0; i < tuple.getSize(); i++) {
						var id = tuple.get(i);
						unaryTupleToInterpretationsMap.computeIfAbsent(Tuple.of(id), k -> new LinkedHashSet<>());
					}
					sb.append(drawEdge(cursor.getKey(), key, entry.getValue()));
				}
			}
		}
		for (var entry : unaryTupleToInterpretationsMap.entrySet()) {
			sb.append(drawElement(entry));
		}
		sb.append("}");
		return sb.toString();
	}

	private StringBuilder drawElement(Map.Entry<Tuple, LinkedHashSet<Interpretation<?>>> entry) {
		var sb = new StringBuilder();

		var tableStyle =  " CELLSPACING=\"0\" BORDER=\"2\" CELLBORDER=\"0\" CELLPADDING=\"4\" STYLE=\"ROUNDED\"";

		var key = entry.getKey();
		var id = key.get(0);
		var mainLabel = String.valueOf(id);
		var interpretations = entry.getValue();
		var backgroundColor = toBackgroundColorString(averageColor(interpretations));

		sb.append(id);
		sb.append(" [\n");
		sb.append("\tfillcolor=\"").append(backgroundColor).append("\"\n");
		sb.append("\tlabel=");
		if (interpretations.isEmpty()) {
			sb.append("<<TABLE").append(tableStyle).append(">\n\t<TR><TD>").append(mainLabel).append("</TD></TR>");
		}
		else {
			sb.append("<<TABLE").append(tableStyle).append(">\n\t\t<TR><TD COLSPAN=\"3\" BORDER=\"2\" SIDES=\"B\">")
					.append(mainLabel).append("</TD></TR>\n");
			for (var interpretation : interpretations) {
				var rawValue = interpretation.get(key);

				if (rawValue == null || rawValue.equals(TruthValue.FALSE) || rawValue.equals(false)) {
					continue;
				}
				var color = "black";
				if (rawValue.equals(TruthValue.ERROR)) {
					color = "red";
				}
				var value = truthValueToDot.getOrDefault(rawValue, rawValue.toString());
				var symbol = interpretation.getSymbol();

				if (symbol.valueType() == String.class) {
					value = "\"" + value + "\"";
				}
				sb.append("\t\t<TR><TD><FONT COLOR=\"").append(color).append("\">")
						.append(interpretation.getSymbol().name())
						.append("</FONT></TD><TD><FONT COLOR=\"").append(color).append("\">")
						.append("=</FONT></TD><TD><FONT COLOR=\"").append(color).append("\">").append(value)
						.append("</FONT></TD></TR>\n");
			}
		}
		sb.append("\t\t</TABLE>>\n");
		sb.append("]\n");

		return sb;
	}

	private String drawEdge(Tuple edge, AnySymbol symbol, Interpretation<?> interpretation) {
		var value = interpretation.get(edge);

		if (value == null || value.equals(TruthValue.FALSE) || value.equals(false)) {
			return "";
		}

		var sb = new StringBuilder();
		var style = "solid";
		var color = "black";
		if (value.equals(TruthValue.UNKNOWN)) {
			style = "dotted";
		}
		else if (value.equals(TruthValue.ERROR)) {
			style = "dashed";
			color = "red";
		}

		var from = edge.get(0);
		var to = edge.get(1);
		var name = symbol.name();
		sb.append(from).append(" -> ").append(to)
				.append(" [\n\tstyle=").append(style)
				.append("\n\tcolor=").append(color)
				.append("\n\tfontcolor=").append(color)
				.append("\n\tlabel=\"").append(name)
				.append("\"]\n");
		return sb.toString();
	}

	private String toBackgroundColorString(Integer[] backgroundColor) {
		if (backgroundColor.length == 3)
			return String.format("#%02x%02x%02x", backgroundColor[0], backgroundColor[1], backgroundColor[2]);
		else if (backgroundColor.length == 4)
			return String.format("#%02x%02x%02x%02x", backgroundColor[0], backgroundColor[1], backgroundColor[2],
					backgroundColor[3]);
		return null;
	}

	private Integer[] typeColor(String name) {
		var random = new Random(name.hashCode());
		return new Integer[] { random.nextInt(128) + 128, random.nextInt(128) + 128, random.nextInt(128) + 128 };
	}

	private Integer[] averageColor(Set<Interpretation<?>> interpretations) {
		if(interpretations.isEmpty()) {
			return new Integer[]{256, 256, 256};
		}
		// TODO: Only use interpretations where the value is not false (or unknown)
		var symbols = interpretations.stream()
				.map(i -> typeColor(i.getSymbol().name())).toArray(Integer[][]::new);



		return new Integer[] {
				Arrays.stream(symbols).map(i -> i[0]).collect(Collectors.averagingInt(Integer::intValue)).intValue(),
				Arrays.stream(symbols).map(i -> i[1]).collect(Collectors.averagingInt(Integer::intValue)).intValue(),
				Arrays.stream(symbols).map(i -> i[2]).collect(Collectors.averagingInt(Integer::intValue)).intValue()
		};
	}

	@Override
	public String createDotForModelState(Version version) {
		var currentVersion = model.getState();
		model.restore(version);
		var graph = createDotForCurrentModelState();
		model.restore(currentVersion);
		return graph;
	}

	@Override
	public boolean saveDot(String dot, String filePath) {
		File file = new File(filePath);
		file.getParentFile().mkdirs();

		try (FileWriter writer = new FileWriter(file)) {
			writer.write(dot);
		} catch (Exception e) {
			e.printStackTrace();
			return false;
		}
		return true;
	}

	@Override
	public boolean renderDot(String dot, String filePath) {
		return renderDot(dot, FileFormat.SVG, filePath);
	}

	@Override
	public boolean renderDot(String dot, FileFormat format, String filePath) {
		try {
			Process process = new ProcessBuilder("dot", "-T" + format.getFormat(), "-o", filePath).start();

			OutputStream osToProcess = process.getOutputStream();
			PrintWriter pwToProcess = new PrintWriter(osToProcess);
			pwToProcess.write(dot);
			pwToProcess.close();
		} catch (IOException e) {
			e.printStackTrace();
			return false;
		}
		return true;
	}

	@Override
	public void addTransition(Version from, Version to, String action) {
		designSpaceBuilder.append(states.get(from)).append(" -> ").append(states.get(to))
				.append(" [label=\"").append(transitionCounter++).append(": ").append(action).append("\"]\n");
	}

	@Override
	public void addTransition(Version from, Version to, String action, Tuple activation) {
		designSpaceBuilder.append(states.get(from)).append(" -> ").append(states.get(to))
				.append(" [label=\"").append(transitionCounter++).append(": ").append(action).append(" / ");


		for (int i = 0; i < activation.getSize(); i++) {
			designSpaceBuilder.append(activation.get(i));
			if (i < activation.getSize() - 1) {
				designSpaceBuilder.append(", ");
			}
		}
		designSpaceBuilder.append("\"]\n");
	}

	@Override
	public void addState(Version state) {
		if (states.containsKey(state)) {
			return;
		}
		states.put(state, numberOfStates++);
		designSpaceBuilder.append(states.get(state)).append(" [URL=\"./").append(states.get(state)).append(".svg\"]\n");
	}

	@Override
	public void addSolution(Version state) {
		addState(state);
		designSpaceBuilder.append(states.get(state)).append(" [shape = doublecircle]\n");
	}

	private String buildDesignSpaceDot() {
		designSpaceBuilder.append("}");
		return designSpaceBuilder.toString();
	}

	@Override
	public boolean saveDesignSpace(String path) {
		saveDot(buildDesignSpaceDot(), path + "/designSpace.dot");
		for (var entry : states.entrySet()) {
			saveDot(createDotForModelState(entry.getKey()), path + "/" + entry.getValue() + ".dot");
		}
		return true;
	}

	@Override
	public boolean renderDesignSpace(String path) {
		return renderDesignSpace(path, FileFormat.SVG);
	}

	@Override
	public boolean renderDesignSpace(String path, FileFormat format) {
		for (var entry : states.entrySet()) {
			var stateId = entry.getValue();
			var stateDot = createDotForModelState(entry.getKey());
			saveDot(stateDot, path + "/" + stateId + ".dot");
			renderDot(stateDot, format, path + "/" + stateId + "." + format.getFormat());
		}
		var designSpaceDot = buildDesignSpaceDot();
		saveDot(designSpaceDot, path + "/designSpace.dot");
		return renderDot(designSpaceDot, format, path + "/designSpace." + format.getFormat());
	}
}

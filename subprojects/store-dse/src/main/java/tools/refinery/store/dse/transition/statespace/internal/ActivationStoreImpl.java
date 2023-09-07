/*
 * SPDX-FileCopyrightText: 2023 The Refinery Authors <https://refinery.tools/>
 *
 * SPDX-License-Identifier: EPL-2.0
 */
package tools.refinery.store.dse.transition.statespace.internal;

import tools.refinery.store.dse.transition.VersionWithObjectiveValue;
import tools.refinery.store.dse.transition.statespace.ActivationStore;

import java.util.*;
import java.util.function.Consumer;

public class ActivationStoreImpl implements ActivationStore {
	final int numberOfTransformations;
	final Consumer<VersionWithObjectiveValue> actionWhenAllActivationVisited;
	final Map<VersionWithObjectiveValue, List<ActivationStoreEntry>> versionToActivations;

	public ActivationStoreImpl(final int numberOfTransformations,
							   Consumer<VersionWithObjectiveValue> actionWhenAllActivationVisited) {
		this.numberOfTransformations = numberOfTransformations;
		this.actionWhenAllActivationVisited = actionWhenAllActivationVisited;
		versionToActivations = new HashMap<>();
	}

	public synchronized VisitResult markNewAsVisited(VersionWithObjectiveValue to, int[] emptyEntrySizes) {
		boolean[] successful = new boolean[]{false};
		var entries = versionToActivations.computeIfAbsent(to, x -> {
			successful[0] = true;
			List<ActivationStoreEntry> result = new ArrayList<>(emptyEntrySizes.length);
			for (int emptyEntrySize : emptyEntrySizes) {
				result.add(ActivationStoreEntry.create(emptyEntrySize));
			}
			return result;
		});
		boolean hasMore = false;
		for (var entry : entries) {
			if (entry.getNumberOfUnvisitedActivations() > 0) {
				hasMore = true;
				break;
			}
		}
		if (!hasMore) {
			actionWhenAllActivationVisited.accept(to);
		}
		return new VisitResult(successful[0], hasMore, -1, -1);
	}

	public synchronized VisitResult visitActivation(VersionWithObjectiveValue from, int transformationIndex,
													int activationIndex) {
		var entries = versionToActivations.get(from);
		var entry = entries.get(transformationIndex);
		final int unvisited = entry.getNumberOfUnvisitedActivations();

		final boolean successfulVisit = unvisited > 0;
		final boolean hasMoreInActivation = unvisited > 1;
		final boolean hasMore;
		final int transformation;
		final int activation;

		if (successfulVisit) {
			transformation = transformationIndex;
			activation = entry.getAndAddActivationAfter(activationIndex);

		} else {
			transformation = -1;
			activation = -1;
		}

		if (!hasMoreInActivation) {
			boolean hasMoreInOtherTransformation = false;
			for (var e : entries) {
				if (e != entry && e.getNumberOfUnvisitedActivations() > 0) {
					hasMoreInOtherTransformation = true;
					break;
				}
			}
			hasMore = hasMoreInOtherTransformation;
		} else {
			hasMore = true;
		}

		if (!hasMore) {
			actionWhenAllActivationVisited.accept(from);
		}

		return new VisitResult(successfulVisit, hasMore, transformation, activation);
	}

	@Override
	public synchronized boolean hasUnmarkedActivation(VersionWithObjectiveValue version) {
		var entries = versionToActivations.get(version);
		boolean hasMore = false;
		for (var entry : entries) {
			if (entry.getNumberOfUnvisitedActivations() > 0) {
				hasMore = true;
				break;
			}
		}
		return hasMore;
	}

	@Override
	public synchronized VisitResult getRandomAndMarkAsVisited(VersionWithObjectiveValue version, Random random) {
		var entries = versionToActivations.get(version);

		int numberOfAllUnvisitedActivations = 0;
		for (var entry : entries) {
			numberOfAllUnvisitedActivations += entry.getNumberOfUnvisitedActivations();
		}

		if (numberOfAllUnvisitedActivations == 0) {
			this.actionWhenAllActivationVisited.accept(version);
			return new VisitResult(false, false, -1, -1);
		}

		int offset = random.nextInt(numberOfAllUnvisitedActivations);
		int transformation = 0;
		for (; transformation < entries.size(); transformation++) {
			var entry = entries.get(transformation);
			int unvisited = entry.getNumberOfUnvisitedActivations();
			if (unvisited > 0 && offset < unvisited) {
				int activation = random.nextInt(entry.getNumberOfActivations());
				return this.visitActivation(version, transformation, activation);
			}
			offset -= unvisited;
		}

		throw new AssertionError("Unvisited activation %d not found".formatted(offset));
	}
}

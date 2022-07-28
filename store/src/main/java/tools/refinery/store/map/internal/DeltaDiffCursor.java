package tools.refinery.store.map.internal;

import java.util.Collections;
import java.util.List;

import tools.refinery.store.map.DiffCursor;
import tools.refinery.store.map.VersionedMap;

public class DeltaDiffCursor<K, V> implements DiffCursor<K, V> {
	final List<MapDelta<K, V>[]> backwardTransactions;
	final List<MapDelta<K, V>[]> forwardTransactions;

	/**
	 * Denotes the direction of traversal. False means backwards, true means
	 * forward.
	 */
	boolean direction;
	int listIndex;
	int arrayIndex;

	public DeltaDiffCursor(List<MapDelta<K, V>[]> backwardTransactions, List<MapDelta<K, V>[]> forwardTransactions) {
		this.backwardTransactions = backwardTransactions;
		this.forwardTransactions = forwardTransactions;

		if (!backwardTransactions.isEmpty()) {
			direction = false;
			listIndex = 0;
			arrayIndex = backwardTransactions.get(listIndex).length - 1;
		} else if (!forwardTransactions.isEmpty()) {
			direction = true;
			listIndex = forwardTransactions.size() - 1;
			arrayIndex = 0;
		} else {
			direction = true;
			listIndex = -1;
		}
	}

	protected MapDelta<K, V> getCurrentDelta() {
		final List<MapDelta<K, V>[]> list;
		if (!direction) {
			list = this.backwardTransactions;
		} else {
			list = this.forwardTransactions;
		}
		return list.get(listIndex)[arrayIndex];
	}

	@Override
	public K getKey() {
		return getCurrentDelta().getKey();
	}

	@Override
	public V getValue() {
		return getToValue();
	}

	@Override
	public boolean isTerminated() {
		return this.direction && listIndex == -1;
	}

	@Override
	public boolean move() {
		if (isTerminated()) {
			return false;
		} else {
			if (this.direction) {
				if (arrayIndex < forwardTransactions.get(listIndex).length) {
					arrayIndex++;
					return true;
				} else {
					if (listIndex >= 0) {
						listIndex--;
						return true;
					} else {
						listIndex = -1;
						return false;
					}
				}
			} else {
				if (arrayIndex > 0) {
					arrayIndex--;
					return true;
				} else {
					if (listIndex <= backwardTransactions.size()) {
						listIndex++;
						this.arrayIndex = backwardTransactions.get(listIndex).length - 1;
						return true;
					} else {
						this.direction = true;
						if (!this.forwardTransactions.isEmpty()) {
							listIndex = forwardTransactions.size() - 1;
							arrayIndex = 0;
							return true;
						} else {
							listIndex = -1;
							return false;
						}
					}
				}
			}
		}
	}

	@Override
	public boolean isDirty() {
		return false;
	}

	@Override
	public List<VersionedMap<?, ?>> getDependingMaps() {
		return Collections.emptyList();
	}

	@Override
	public V getFromValue() {
		return getCurrentDelta().getOldValue();
	}

	@Override
	public V getToValue() {
		return getCurrentDelta().getNewValue();
	}
}

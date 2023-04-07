package tools.refinery.store.query;

import tools.refinery.store.map.Cursor;
import tools.refinery.store.query.dnf.Query;
import tools.refinery.store.tuple.Tuple;

public non-sealed interface ResultSet<T> extends AnyResultSet {
	Query<T> getQuery();

	T get(Tuple parameters);

	Cursor<Tuple, T> getAll();
}
